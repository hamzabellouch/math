import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw6784 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6784Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6784step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6784step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6784 raw6784Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw6784 raw6784Labels = mixedMoment B raw6784step0 raw6784step0Labels := by
      have hz : ∀ j, raw6784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6784step0 = (fun i j => raw6784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6784step0 raw6784; decide +kernel
      have hl : raw6784step0Labels = raw6784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6784 raw6784Labels permutation346 hz
    mixedMoment B raw6784step0 raw6784step0Labels = mixedMoment B raw6784step1 raw6784step1Labels := by
      have ha : raw6784step1 = (fun i j => raw6784step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6784step1 raw6784step0; decide +kernel
      have hl : raw6784step1Labels = raw6784step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6784step0 raw6784step0Labels permutation35 permutation4
    mixedMoment B raw6784step1 raw6784step1Labels = mixedMoment B raw6784step2 raw6784step2Labels := by
      have ha : raw6784step2 = -raw6784step1 := by apply Matrix.ext; change ∀ i j, raw6784step2 i j = -(raw6784step1 i j); unfold raw6784step2 raw6784step1; decide +kernel
      have hl : raw6784step2Labels = raw6784step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw6785 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6785Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6785step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6785step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6785step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6785 raw6785Labels = mixedMoment B node3395 node3395Labels := by
  calc
    mixedMoment B raw6785 raw6785Labels = mixedMoment B raw6785step0 raw6785step0Labels := by
      have hz : ∀ j, raw6785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6785step0 = (fun i j => raw6785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6785step0 raw6785; decide +kernel
      have hl : raw6785step0Labels = raw6785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6785 raw6785Labels permutation346 hz
    mixedMoment B raw6785step0 raw6785step0Labels = mixedMoment B raw6785step1 raw6785step1Labels := by
      have ha : raw6785step1 = (fun i j => raw6785step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6785step1 raw6785step0; decide +kernel
      have hl : raw6785step1Labels = raw6785step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6785step0 raw6785step0Labels permutation41 permutation2
    mixedMoment B raw6785step1 raw6785step1Labels = mixedMoment B raw6785step2 raw6785step2Labels := by
      have ha : raw6785step2 = -raw6785step1 := by apply Matrix.ext; change ∀ i j, raw6785step2 i j = -(raw6785step1 i j); unfold raw6785step2 raw6785step1; decide +kernel
      have hl : raw6785step2Labels = raw6785step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3395 node3395Labels := by rfl

def raw6786 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6786Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6786step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6786step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6786step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6786step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6786 raw6786Labels = mixedMoment B node3388 node3388Labels := by
  calc
    mixedMoment B raw6786 raw6786Labels = mixedMoment B raw6786step0 raw6786step0Labels := by
      have ha : raw6786step0 = (fun i j => raw6786 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6786step0 raw6786; decide +kernel
      have hl : raw6786step0Labels = raw6786Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6786 raw6786Labels permutation200 permutation2
    mixedMoment B raw6786step0 raw6786step0Labels = mixedMoment B raw6786step1 raw6786step1Labels := by
      have ha : raw6786step1 = -raw6786step0 := by apply Matrix.ext; change ∀ i j, raw6786step1 i j = -(raw6786step0 i j); unfold raw6786step1 raw6786step0; decide +kernel
      have hl : raw6786step1Labels = raw6786step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3388 node3388Labels := by rfl

def raw6787 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6787Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6787step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6787step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6787step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6787 raw6787Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw6787 raw6787Labels = mixedMoment B raw6787step0 raw6787step0Labels := by
      have hz : ∀ j, raw6787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6787step0 = (fun i j => raw6787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6787step0 raw6787; decide +kernel
      have hl : raw6787step0Labels = raw6787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6787 raw6787Labels permutation346 hz
    mixedMoment B raw6787step0 raw6787step0Labels = mixedMoment B raw6787step1 raw6787step1Labels := by
      have ha : raw6787step1 = (fun i j => raw6787step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6787step1 raw6787step0; decide +kernel
      have hl : raw6787step1Labels = raw6787step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6787step0 raw6787step0Labels permutation38 permutation2
    mixedMoment B raw6787step1 raw6787step1Labels = mixedMoment B raw6787step2 raw6787step2Labels := by
      have ha : raw6787step2 = -raw6787step1 := by apply Matrix.ext; change ∀ i j, raw6787step2 i j = -(raw6787step1 i j); unfold raw6787step2 raw6787step1; decide +kernel
      have hl : raw6787step2Labels = raw6787step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw6788 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6788Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6788step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw6788step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6788step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6788 raw6788Labels = mixedMoment B node3392 node3392Labels := by
  calc
    mixedMoment B raw6788 raw6788Labels = mixedMoment B raw6788step0 raw6788step0Labels := by
      have hz : ∀ j, raw6788 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6788step0 = (fun i j => raw6788 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6788step0 raw6788; decide +kernel
      have hl : raw6788step0Labels = raw6788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6788 raw6788Labels permutation346 hz
    mixedMoment B raw6788step0 raw6788step0Labels = mixedMoment B raw6788step1 raw6788step1Labels := by
      have ha : raw6788step1 = (fun i j => raw6788step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6788step1 raw6788step0; decide +kernel
      have hl : raw6788step1Labels = raw6788step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6788step0 raw6788step0Labels permutation39 permutation2
    mixedMoment B raw6788step1 raw6788step1Labels = mixedMoment B raw6788step2 raw6788step2Labels := by
      have ha : raw6788step2 = -raw6788step1 := by apply Matrix.ext; change ∀ i j, raw6788step2 i j = -(raw6788step1 i j); unfold raw6788step2 raw6788step1; decide +kernel
      have hl : raw6788step2Labels = raw6788step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3392 node3392Labels := by rfl

def raw6789 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6789Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6789step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6789step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6789step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6789 raw6789Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw6789 raw6789Labels = mixedMoment B raw6789step0 raw6789step0Labels := by
      have hz : ∀ j, raw6789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6789step0 = (fun i j => raw6789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6789step0 raw6789; decide +kernel
      have hl : raw6789step0Labels = raw6789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6789 raw6789Labels permutation346 hz
    mixedMoment B raw6789step0 raw6789step0Labels = mixedMoment B raw6789step1 raw6789step1Labels := by
      have ha : raw6789step1 = (fun i j => raw6789step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6789step1 raw6789step0; decide +kernel
      have hl : raw6789step1Labels = raw6789step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6789step0 raw6789step0Labels permutation38 permutation2
    mixedMoment B raw6789step1 raw6789step1Labels = mixedMoment B raw6789step2 raw6789step2Labels := by
      have ha : raw6789step2 = -raw6789step1 := by apply Matrix.ext; change ∀ i j, raw6789step2 i j = -(raw6789step1 i j); unfold raw6789step2 raw6789step1; decide +kernel
      have hl : raw6789step2Labels = raw6789step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3391 node3391Labels := by rfl

def raw6790 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6790Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6790step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6790step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6790step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6790step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6790step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6790step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6790step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6790 raw6790Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw6790 raw6790Labels = mixedMoment B raw6790step0 raw6790step0Labels := by
      have hz : ∀ j, raw6790 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6790step0 = (fun i j => raw6790 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6790step0 raw6790; decide +kernel
      have hl : raw6790step0Labels = raw6790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6790 raw6790Labels permutation346 hz
    mixedMoment B raw6790step0 raw6790step0Labels = mixedMoment B raw6790step1 raw6790step1Labels := by
      have hz : ∀ j, raw6790step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6790step1 = (fun i j => raw6790step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6790step1 raw6790step0; decide +kernel
      have hl : raw6790step1Labels = raw6790step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6790step0 raw6790step0Labels permutation56 hz
    mixedMoment B raw6790step1 raw6790step1Labels = mixedMoment B raw6790step2 raw6790step2Labels := by
      have ha : raw6790step2 = (fun i j => raw6790step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6790step2 raw6790step1; decide +kernel
      have hl : raw6790step2Labels = raw6790step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6790step1 raw6790step1Labels permutation11 permutation4
    mixedMoment B raw6790step2 raw6790step2Labels = mixedMoment B raw6790step3 raw6790step3Labels := by
      have ha : raw6790step3 = -raw6790step2 := by apply Matrix.ext; change ∀ i j, raw6790step3 i j = -(raw6790step2 i j); unfold raw6790step3 raw6790step2; decide +kernel
      have hl : raw6790step3Labels = raw6790step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw6791 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6791Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6791step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw6791step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6791step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6791step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6791 raw6791Labels = mixedMoment B node2021 node2021Labels := by
  calc
    mixedMoment B raw6791 raw6791Labels = mixedMoment B raw6791step0 raw6791step0Labels := by
      have ha : raw6791step0 = (fun i j => raw6791 (permutation165 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6791step0 raw6791; decide +kernel
      have hl : raw6791step0Labels = raw6791Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6791 raw6791Labels permutation165 permutation4
    mixedMoment B raw6791step0 raw6791step0Labels = mixedMoment B raw6791step1 raw6791step1Labels := by
      have ha : raw6791step1 = -raw6791step0 := by apply Matrix.ext; change ∀ i j, raw6791step1 i j = -(raw6791step0 i j); unfold raw6791step1 raw6791step0; decide +kernel
      have hl : raw6791step1Labels = raw6791step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2021 node2021Labels := by rfl

def raw6792 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6792Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6792step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6792step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6792step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw6792step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6792step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw6792step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6792 raw6792Labels = mixedMoment B node2026 node2026Labels := by
  calc
    mixedMoment B raw6792 raw6792Labels = mixedMoment B raw6792step0 raw6792step0Labels := by
      have hz : ∀ j, raw6792 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6792step0 = (fun i j => raw6792 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6792step0 raw6792; decide +kernel
      have hl : raw6792step0Labels = raw6792Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6792 raw6792Labels permutation346 hz
    mixedMoment B raw6792step0 raw6792step0Labels = mixedMoment B raw6792step1 raw6792step1Labels := by
      have ha : raw6792step1 = (fun i j => raw6792step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6792step1 raw6792step0; decide +kernel
      have hl : raw6792step1Labels = raw6792step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6792step0 raw6792step0Labels permutation35 permutation4
    mixedMoment B raw6792step1 raw6792step1Labels = mixedMoment B raw6792step2 raw6792step2Labels := by
      have ha : raw6792step2 = -raw6792step1 := by apply Matrix.ext; change ∀ i j, raw6792step2 i j = -(raw6792step1 i j); unfold raw6792step2 raw6792step1; decide +kernel
      have hl : raw6792step2Labels = raw6792step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2026 node2026Labels := by rfl

def raw6793 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6793Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6793step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6793step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6793 raw6793Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw6793 raw6793Labels = mixedMoment B raw6793step0 raw6793step0Labels := by
      have hz : ∀ j, raw6793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6793step0 = (fun i j => raw6793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6793step0 raw6793; decide +kernel
      have hl : raw6793step0Labels = raw6793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6793 raw6793Labels permutation346 hz
    mixedMoment B raw6793step0 raw6793step0Labels = mixedMoment B raw6793step1 raw6793step1Labels := by
      have ha : raw6793step1 = (fun i j => raw6793step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6793step1 raw6793step0; decide +kernel
      have hl : raw6793step1Labels = raw6793step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6793step0 raw6793step0Labels permutation35 permutation4
    mixedMoment B raw6793step1 raw6793step1Labels = mixedMoment B raw6793step2 raw6793step2Labels := by
      have ha : raw6793step2 = -raw6793step1 := by apply Matrix.ext; change ∀ i j, raw6793step2 i j = -(raw6793step1 i j); unfold raw6793step2 raw6793step1; decide +kernel
      have hl : raw6793step2Labels = raw6793step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2058 node2058Labels := by rfl

def raw6794 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6794Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6794step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw6794step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6794step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6794step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6794 raw6794Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw6794 raw6794Labels = mixedMoment B raw6794step0 raw6794step0Labels := by
      have hz : ∀ j, raw6794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6794step0 = (fun i j => raw6794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6794step0 raw6794; decide +kernel
      have hl : raw6794step0Labels = raw6794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6794 raw6794Labels permutation346 hz
    mixedMoment B raw6794step0 raw6794step0Labels = mixedMoment B raw6794step1 raw6794step1Labels := by
      have ha : raw6794step1 = (fun i j => raw6794step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6794step1 raw6794step0; decide +kernel
      have hl : raw6794step1Labels = raw6794step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6794step0 raw6794step0Labels permutation34 permutation4
    mixedMoment B raw6794step1 raw6794step1Labels = mixedMoment B raw6794step2 raw6794step2Labels := by
      have ha : raw6794step2 = -raw6794step1 := by apply Matrix.ext; change ∀ i j, raw6794step2 i j = -(raw6794step1 i j); unfold raw6794step2 raw6794step1; decide +kernel
      have hl : raw6794step2Labels = raw6794step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2028 node2028Labels := by rfl

def raw6795 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6795Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6795step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6795step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6795step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6795 raw6795Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw6795 raw6795Labels = mixedMoment B raw6795step0 raw6795step0Labels := by
      have hz : ∀ j, raw6795 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw6795step0 = (fun i j => raw6795 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw6795step0 raw6795; decide +kernel
      have hl : raw6795step0Labels = raw6795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6795 raw6795Labels permutation265 hz
    mixedMoment B raw6795step0 raw6795step0Labels = mixedMoment B raw6795step1 raw6795step1Labels := by
      have ha : raw6795step1 = (fun i j => raw6795step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6795step1 raw6795step0; decide +kernel
      have hl : raw6795step1Labels = raw6795step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6795step0 raw6795step0Labels permutation35 permutation4
    mixedMoment B raw6795step1 raw6795step1Labels = mixedMoment B raw6795step2 raw6795step2Labels := by
      have ha : raw6795step2 = -raw6795step1 := by apply Matrix.ext; change ∀ i j, raw6795step2 i j = -(raw6795step1 i j); unfold raw6795step2 raw6795step1; decide +kernel
      have hl : raw6795step2Labels = raw6795step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw6796 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6796Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6796step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6796step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6796step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6796step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw6796step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6796step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw6796step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6796 raw6796Labels = mixedMoment B node3627 node3627Labels := by
  calc
    mixedMoment B raw6796 raw6796Labels = mixedMoment B raw6796step0 raw6796step0Labels := by
      have hz : ∀ j, raw6796 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6796step0 = (fun i j => raw6796 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6796step0 raw6796; decide +kernel
      have hl : raw6796step0Labels = raw6796Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6796 raw6796Labels permutation346 hz
    mixedMoment B raw6796step0 raw6796step0Labels = mixedMoment B raw6796step1 raw6796step1Labels := by
      have hz : ∀ j, raw6796step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6796step1 = (fun i j => raw6796step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6796step1 raw6796step0; decide +kernel
      have hl : raw6796step1Labels = raw6796step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6796step0 raw6796step0Labels permutation56 hz
    mixedMoment B raw6796step1 raw6796step1Labels = mixedMoment B raw6796step2 raw6796step2Labels := by
      have ha : raw6796step2 = (fun i j => raw6796step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6796step2 raw6796step1; decide +kernel
      have hl : raw6796step2Labels = raw6796step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6796step1 raw6796step1Labels permutation10 permutation4
    mixedMoment B raw6796step2 raw6796step2Labels = mixedMoment B raw6796step3 raw6796step3Labels := by
      have ha : raw6796step3 = -raw6796step2 := by apply Matrix.ext; change ∀ i j, raw6796step3 i j = -(raw6796step2 i j); unfold raw6796step3 raw6796step2; decide +kernel
      have hl : raw6796step3Labels = raw6796step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3627 node3627Labels := by rfl

def raw6797 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6797Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6797step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6797step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6797step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6797step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6797step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6797step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6797step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6797 raw6797Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw6797 raw6797Labels = mixedMoment B raw6797step0 raw6797step0Labels := by
      have hz : ∀ j, raw6797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6797step0 = (fun i j => raw6797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6797step0 raw6797; decide +kernel
      have hl : raw6797step0Labels = raw6797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6797 raw6797Labels permutation346 hz
    mixedMoment B raw6797step0 raw6797step0Labels = mixedMoment B raw6797step1 raw6797step1Labels := by
      have hz : ∀ j, raw6797step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6797step1 = (fun i j => raw6797step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6797step1 raw6797step0; decide +kernel
      have hl : raw6797step1Labels = raw6797step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6797step0 raw6797step0Labels permutation56 hz
    mixedMoment B raw6797step1 raw6797step1Labels = mixedMoment B raw6797step2 raw6797step2Labels := by
      have ha : raw6797step2 = (fun i j => raw6797step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6797step2 raw6797step1; decide +kernel
      have hl : raw6797step2Labels = raw6797step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6797step1 raw6797step1Labels permutation11 permutation4
    mixedMoment B raw6797step2 raw6797step2Labels = mixedMoment B raw6797step3 raw6797step3Labels := by
      have ha : raw6797step3 = -raw6797step2 := by apply Matrix.ext; change ∀ i j, raw6797step3 i j = -(raw6797step2 i j); unfold raw6797step3 raw6797step2; decide +kernel
      have hl : raw6797step3Labels = raw6797step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3584 node3584Labels := by rfl

def raw6798 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6798Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6798step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6798step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6798step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw6798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6798step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw6798step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6798 raw6798Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw6798 raw6798Labels = mixedMoment B raw6798step0 raw6798step0Labels := by
      have hz : ∀ j, raw6798 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6798step0 = (fun i j => raw6798 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6798step0 raw6798; decide +kernel
      have hl : raw6798step0Labels = raw6798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6798 raw6798Labels permutation346 hz
    mixedMoment B raw6798step0 raw6798step0Labels = mixedMoment B raw6798step1 raw6798step1Labels := by
      have hz : ∀ j, raw6798step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6798step1 = (fun i j => raw6798step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6798step1 raw6798step0; decide +kernel
      have hl : raw6798step1Labels = raw6798step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6798step0 raw6798step0Labels permutation56 hz
    mixedMoment B raw6798step1 raw6798step1Labels = mixedMoment B raw6798step2 raw6798step2Labels := by
      have ha : raw6798step2 = (fun i j => raw6798step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6798step2 raw6798step1; decide +kernel
      have hl : raw6798step2Labels = raw6798step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6798step1 raw6798step1Labels permutation11 permutation4
    mixedMoment B raw6798step2 raw6798step2Labels = mixedMoment B raw6798step3 raw6798step3Labels := by
      have ha : raw6798step3 = -raw6798step2 := by apply Matrix.ext; change ∀ i j, raw6798step3 i j = -(raw6798step2 i j); unfold raw6798step3 raw6798step2; decide +kernel
      have hl : raw6798step3Labels = raw6798step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3626 node3626Labels := by rfl

def raw6799 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6799Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6799step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw6799step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6799step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6799step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6799 raw6799Labels = mixedMoment B node3377 node3377Labels := by
  calc
    mixedMoment B raw6799 raw6799Labels = mixedMoment B raw6799step0 raw6799step0Labels := by
      have ha : raw6799step0 = (fun i j => raw6799 (permutation165 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6799step0 raw6799; decide +kernel
      have hl : raw6799step0Labels = raw6799Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6799 raw6799Labels permutation165 permutation4
    mixedMoment B raw6799step0 raw6799step0Labels = mixedMoment B raw6799step1 raw6799step1Labels := by
      have ha : raw6799step1 = -raw6799step0 := by apply Matrix.ext; change ∀ i j, raw6799step1 i j = -(raw6799step0 i j); unfold raw6799step1 raw6799step0; decide +kernel
      have hl : raw6799step1Labels = raw6799step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3377 node3377Labels := by rfl

def raw6800 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6800Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6800step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6800step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6800 raw6800Labels = mixedMoment B node3159 node3159Labels := by
  calc
    mixedMoment B raw6800 raw6800Labels = mixedMoment B raw6800step0 raw6800step0Labels := by
      have hz : ∀ j, raw6800 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6800step0 = (fun i j => raw6800 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6800step0 raw6800; decide +kernel
      have hl : raw6800step0Labels = raw6800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6800 raw6800Labels permutation346 hz
    mixedMoment B raw6800step0 raw6800step0Labels = mixedMoment B raw6800step1 raw6800step1Labels := by
      have ha : raw6800step1 = (fun i j => raw6800step0 (permutation83 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6800step1 raw6800step0; decide +kernel
      have hl : raw6800step1Labels = raw6800step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6800step0 raw6800step0Labels permutation83 permutation2
    mixedMoment B raw6800step1 raw6800step1Labels = mixedMoment B raw6800step2 raw6800step2Labels := by
      have ha : raw6800step2 = -raw6800step1 := by apply Matrix.ext; change ∀ i j, raw6800step2 i j = -(raw6800step1 i j); unfold raw6800step2 raw6800step1; decide +kernel
      have hl : raw6800step2Labels = raw6800step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3159 node3159Labels := by rfl

def raw6801 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6801Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6801step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6801step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6801step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6801 raw6801Labels = mixedMoment B node3395 node3395Labels := by
  calc
    mixedMoment B raw6801 raw6801Labels = mixedMoment B raw6801step0 raw6801step0Labels := by
      have hz : ∀ j, raw6801 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6801step0 = (fun i j => raw6801 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6801step0 raw6801; decide +kernel
      have hl : raw6801step0Labels = raw6801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6801 raw6801Labels permutation346 hz
    mixedMoment B raw6801step0 raw6801step0Labels = mixedMoment B raw6801step1 raw6801step1Labels := by
      have ha : raw6801step1 = (fun i j => raw6801step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6801step1 raw6801step0; decide +kernel
      have hl : raw6801step1Labels = raw6801step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6801step0 raw6801step0Labels permutation35 permutation4
    mixedMoment B raw6801step1 raw6801step1Labels = mixedMoment B raw6801step2 raw6801step2Labels := by
      have ha : raw6801step2 = -raw6801step1 := by apply Matrix.ext; change ∀ i j, raw6801step2 i j = -(raw6801step1 i j); unfold raw6801step2 raw6801step1; decide +kernel
      have hl : raw6801step2Labels = raw6801step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3395 node3395Labels := by rfl

def raw6802 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6802Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6802step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw6802step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6802 raw6802Labels = mixedMoment B node3379 node3379Labels := by
  calc
    mixedMoment B raw6802 raw6802Labels = mixedMoment B raw6802step0 raw6802step0Labels := by
      have hz : ∀ j, raw6802 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6802step0 = (fun i j => raw6802 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6802step0 raw6802; decide +kernel
      have hl : raw6802step0Labels = raw6802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6802 raw6802Labels permutation346 hz
    mixedMoment B raw6802step0 raw6802step0Labels = mixedMoment B raw6802step1 raw6802step1Labels := by
      have ha : raw6802step1 = (fun i j => raw6802step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6802step1 raw6802step0; decide +kernel
      have hl : raw6802step1Labels = raw6802step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6802step0 raw6802step0Labels permutation34 permutation4
    mixedMoment B raw6802step1 raw6802step1Labels = mixedMoment B raw6802step2 raw6802step2Labels := by
      have ha : raw6802step2 = -raw6802step1 := by apply Matrix.ext; change ∀ i j, raw6802step2 i j = -(raw6802step1 i j); unfold raw6802step2 raw6802step1; decide +kernel
      have hl : raw6802step2Labels = raw6802step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3379 node3379Labels := by rfl

def raw6803 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6803Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6803step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw6803step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6803step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw6803step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6803 raw6803Labels = mixedMoment B node3531 node3531Labels := by
  calc
    mixedMoment B raw6803 raw6803Labels = mixedMoment B raw6803step0 raw6803step0Labels := by
      have ha : raw6803step0 = (fun i j => raw6803 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6803step0 raw6803; decide +kernel
      have hl : raw6803step0Labels = raw6803Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6803 raw6803Labels permutation164 permutation4
    mixedMoment B raw6803step0 raw6803step0Labels = mixedMoment B raw6803step1 raw6803step1Labels := by
      have ha : raw6803step1 = -raw6803step0 := by apply Matrix.ext; change ∀ i j, raw6803step1 i j = -(raw6803step0 i j); unfold raw6803step1 raw6803step0; decide +kernel
      have hl : raw6803step1Labels = raw6803step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3531 node3531Labels := by rfl

def raw6804 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6804Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw6804step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6804 raw6804Labels = mixedMoment B node3504 node3504Labels := by
  calc
    mixedMoment B raw6804 raw6804Labels = mixedMoment B raw6804step0 raw6804step0Labels := by
      have ha : raw6804step0 = (fun i j => raw6804 (permutation165 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6804step0 raw6804; decide +kernel
      have hl : raw6804step0Labels = raw6804Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6804 raw6804Labels permutation165 permutation4
    mixedMoment B raw6804step0 raw6804step0Labels = mixedMoment B raw6804step1 raw6804step1Labels := by
      have ha : raw6804step1 = -raw6804step0 := by apply Matrix.ext; change ∀ i j, raw6804step1 i j = -(raw6804step0 i j); unfold raw6804step1 raw6804step0; decide +kernel
      have hl : raw6804step1Labels = raw6804step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3504 node3504Labels := by rfl

def raw6805 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6805Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw6805step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6805step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6805step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6805 raw6805Labels = mixedMoment B node3528 node3528Labels := by
  calc
    mixedMoment B raw6805 raw6805Labels = mixedMoment B raw6805step0 raw6805step0Labels := by
      have ha : raw6805step0 = (fun i j => raw6805 (permutation168 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6805step0 raw6805; decide +kernel
      have hl : raw6805step0Labels = raw6805Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6805 raw6805Labels permutation168 permutation4
    mixedMoment B raw6805step0 raw6805step0Labels = mixedMoment B raw6805step1 raw6805step1Labels := by
      have ha : raw6805step1 = -raw6805step0 := by apply Matrix.ext; change ∀ i j, raw6805step1 i j = -(raw6805step0 i j); unfold raw6805step1 raw6805step0; decide +kernel
      have hl : raw6805step1Labels = raw6805step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3528 node3528Labels := by rfl

def raw6806 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6806Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6806step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6806step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6806step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6806 raw6806Labels = mixedMoment B node3153 node3153Labels := by
  calc
    mixedMoment B raw6806 raw6806Labels = mixedMoment B raw6806step0 raw6806step0Labels := by
      have ha : raw6806step0 = (fun i j => raw6806 (permutation434 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6806step0 raw6806; decide +kernel
      have hl : raw6806step0Labels = raw6806Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6806 raw6806Labels permutation434 permutation2
    mixedMoment B raw6806step0 raw6806step0Labels = mixedMoment B raw6806step1 raw6806step1Labels := by
      have ha : raw6806step1 = -raw6806step0 := by apply Matrix.ext; change ∀ i j, raw6806step1 i j = -(raw6806step0 i j); unfold raw6806step1 raw6806step0; decide +kernel
      have hl : raw6806step1Labels = raw6806step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3153 node3153Labels := by rfl

def raw6807 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6807Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6807step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6807 raw6807Labels = mixedMoment B node3497 node3497Labels := by
  calc
    mixedMoment B raw6807 raw6807Labels = mixedMoment B raw6807step0 raw6807step0Labels := by
      have ha : raw6807step0 = (fun i j => raw6807 (permutation155 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6807step0 raw6807; decide +kernel
      have hl : raw6807step0Labels = raw6807Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6807 raw6807Labels permutation155 permutation4
    mixedMoment B raw6807step0 raw6807step0Labels = mixedMoment B raw6807step1 raw6807step1Labels := by
      have ha : raw6807step1 = -raw6807step0 := by apply Matrix.ext; change ∀ i j, raw6807step1 i j = -(raw6807step0 i j); unfold raw6807step1 raw6807step0; decide +kernel
      have hl : raw6807step1Labels = raw6807step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3497 node3497Labels := by rfl

def raw6808 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6808Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw6808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6808step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6808step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6808 raw6808Labels = mixedMoment B node3488 node3488Labels := by
  calc
    mixedMoment B raw6808 raw6808Labels = mixedMoment B raw6808step0 raw6808step0Labels := by
      have ha : raw6808step0 = (fun i j => raw6808 (permutation154 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6808step0 raw6808; decide +kernel
      have hl : raw6808step0Labels = raw6808Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6808 raw6808Labels permutation154 permutation4
    mixedMoment B raw6808step0 raw6808step0Labels = mixedMoment B raw6808step1 raw6808step1Labels := by
      have ha : raw6808step1 = -raw6808step0 := by apply Matrix.ext; change ∀ i j, raw6808step1 i j = -(raw6808step0 i j); unfold raw6808step1 raw6808step0; decide +kernel
      have hl : raw6808step1Labels = raw6808step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3488 node3488Labels := by rfl

def raw6809 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6809Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw6809step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw6809step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6809step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6809step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6809 raw6809Labels = mixedMoment B node3157 node3157Labels := by
  calc
    mixedMoment B raw6809 raw6809Labels = mixedMoment B raw6809step0 raw6809step0Labels := by
      have hz : ∀ j, raw6809 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6809step0 = (fun i j => raw6809 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6809step0 raw6809; decide +kernel
      have hl : raw6809step0Labels = raw6809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6809 raw6809Labels permutation346 hz
    mixedMoment B raw6809step0 raw6809step0Labels = mixedMoment B raw6809step1 raw6809step1Labels := by
      have ha : raw6809step1 = (fun i j => raw6809step0 (permutation81 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6809step1 raw6809step0; decide +kernel
      have hl : raw6809step1Labels = raw6809step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6809step0 raw6809step0Labels permutation81 permutation2
    mixedMoment B raw6809step1 raw6809step1Labels = mixedMoment B raw6809step2 raw6809step2Labels := by
      have ha : raw6809step2 = -raw6809step1 := by apply Matrix.ext; change ∀ i j, raw6809step2 i j = -(raw6809step1 i j); unfold raw6809step2 raw6809step1; decide +kernel
      have hl : raw6809step2Labels = raw6809step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3157 node3157Labels := by rfl

def raw6810 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6810Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6810step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6810step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6810step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6810step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6810 raw6810Labels = mixedMoment B node3156 node3156Labels := by
  calc
    mixedMoment B raw6810 raw6810Labels = mixedMoment B raw6810step0 raw6810step0Labels := by
      have hz : ∀ j, raw6810 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6810step0 = (fun i j => raw6810 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6810step0 raw6810; decide +kernel
      have hl : raw6810step0Labels = raw6810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6810 raw6810Labels permutation346 hz
    mixedMoment B raw6810step0 raw6810step0Labels = mixedMoment B raw6810step1 raw6810step1Labels := by
      have ha : raw6810step1 = (fun i j => raw6810step0 (permutation80 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6810step1 raw6810step0; decide +kernel
      have hl : raw6810step1Labels = raw6810step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6810step0 raw6810step0Labels permutation80 permutation2
    mixedMoment B raw6810step1 raw6810step1Labels = mixedMoment B raw6810step2 raw6810step2Labels := by
      have ha : raw6810step2 = -raw6810step1 := by apply Matrix.ext; change ∀ i j, raw6810step2 i j = -(raw6810step1 i j); unfold raw6810step2 raw6810step1; decide +kernel
      have hl : raw6810step2Labels = raw6810step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3156 node3156Labels := by rfl

def raw6811 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6811Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw6811step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw6811step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6811step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6811 raw6811Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw6811 raw6811Labels = mixedMoment B raw6811step0 raw6811step0Labels := by
      have hz : ∀ j, raw6811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6811step0 = (fun i j => raw6811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6811step0 raw6811; decide +kernel
      have hl : raw6811step0Labels = raw6811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6811 raw6811Labels permutation346 hz
    mixedMoment B raw6811step0 raw6811step0Labels = mixedMoment B raw6811step1 raw6811step1Labels := by
      have ha : raw6811step1 = (fun i j => raw6811step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6811step1 raw6811step0; decide +kernel
      have hl : raw6811step1Labels = raw6811step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6811step0 raw6811step0Labels permutation34 permutation4
    mixedMoment B raw6811step1 raw6811step1Labels = mixedMoment B raw6811step2 raw6811step2Labels := by
      have ha : raw6811step2 = -raw6811step1 := by apply Matrix.ext; change ∀ i j, raw6811step2 i j = -(raw6811step1 i j); unfold raw6811step2 raw6811step1; decide +kernel
      have hl : raw6811step2Labels = raw6811step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw6812 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw6812Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw6812step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw6812step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw6812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6812 raw6812Labels = mixedMoment B node3506 node3506Labels := by
  calc
    mixedMoment B raw6812 raw6812Labels = mixedMoment B raw6812step0 raw6812step0Labels := by
      have hz : ∀ j, raw6812 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6812step0 = (fun i j => raw6812 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6812step0 raw6812; decide +kernel
      have hl : raw6812step0Labels = raw6812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6812 raw6812Labels permutation346 hz
    mixedMoment B raw6812step0 raw6812step0Labels = mixedMoment B raw6812step1 raw6812step1Labels := by
      have ha : raw6812step1 = (fun i j => raw6812step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6812step1 raw6812step0; decide +kernel
      have hl : raw6812step1Labels = raw6812step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6812step0 raw6812step0Labels permutation34 permutation4
    mixedMoment B raw6812step1 raw6812step1Labels = mixedMoment B raw6812step2 raw6812step2Labels := by
      have ha : raw6812step2 = -raw6812step1 := by apply Matrix.ext; change ∀ i j, raw6812step2 i j = -(raw6812step1 i j); unfold raw6812step2 raw6812step1; decide +kernel
      have hl : raw6812step2Labels = raw6812step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3506 node3506Labels := by rfl

def raw6813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6813 raw6813Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw6813 raw6813Labels = mixedMoment B raw6813step0 raw6813step0Labels := by
      have hz : ∀ j, raw6813 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6813step0 = (fun i j => raw6813 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6813step0 raw6813; decide +kernel
      have hl : raw6813step0Labels = raw6813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6813 raw6813Labels permutation346 hz
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw6814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6814step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6814 raw6814Labels = mixedMoment B node5426 node5426Labels := by
  calc
    mixedMoment B raw6814 raw6814Labels = mixedMoment B raw6814step0 raw6814step0Labels := by
      have ha : raw6814step0 = (fun i j => raw6814 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6814step0 raw6814; decide +kernel
      have hl : raw6814step0Labels = raw6814Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6814 raw6814Labels permutation176 permutation2
    _ = mixedMoment B node5426 node5426Labels := by rfl

def raw6815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6815step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6815step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6815step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6815step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6815step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6815 raw6815Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw6815 raw6815Labels = mixedMoment B raw6815step0 raw6815step0Labels := by
      have hz : ∀ j, raw6815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6815step0 = (fun i j => raw6815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6815step0 raw6815; decide +kernel
      have hl : raw6815step0Labels = raw6815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6815 raw6815Labels permutation346 hz
    mixedMoment B raw6815step0 raw6815step0Labels = mixedMoment B raw6815step1 raw6815step1Labels := by
      have ha : raw6815step1 = (fun i j => raw6815step0 (permutation92 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6815step1 raw6815step0; decide +kernel
      have hl : raw6815step1Labels = raw6815step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6815step0 raw6815step0Labels permutation92 permutation4
    mixedMoment B raw6815step1 raw6815step1Labels = mixedMoment B raw6815step2 raw6815step2Labels := by
      have ha : raw6815step2 = -raw6815step1 := by apply Matrix.ext; change ∀ i j, raw6815step2 i j = -(raw6815step1 i j); unfold raw6815step2 raw6815step1; decide +kernel
      have hl : raw6815step2Labels = raw6815step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6815step2 raw6815step2Labels = mixedMoment B raw6815step3 raw6815step3Labels := by
      have ha : raw6815step3 = raw6815step2 := by apply Matrix.ext; unfold raw6815step3 raw6815step2; decide +kernel
      have hl : raw6815step2Labels = labelEmbedding7 ∘ raw6815step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6815step2 raw6815step2Labels raw6815step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw6816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6816step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6816step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6816step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6816step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6816step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6816 raw6816Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw6816 raw6816Labels = mixedMoment B raw6816step0 raw6816step0Labels := by
      have hz : ∀ j, raw6816 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6816step0 = (fun i j => raw6816 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6816step0 raw6816; decide +kernel
      have hl : raw6816step0Labels = raw6816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6816 raw6816Labels permutation346 hz
    mixedMoment B raw6816step0 raw6816step0Labels = mixedMoment B raw6816step1 raw6816step1Labels := by
      have ha : raw6816step1 = (fun i j => raw6816step0 (permutation92 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6816step1 raw6816step0; decide +kernel
      have hl : raw6816step1Labels = raw6816step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6816step0 raw6816step0Labels permutation92 permutation4
    mixedMoment B raw6816step1 raw6816step1Labels = mixedMoment B raw6816step2 raw6816step2Labels := by
      have ha : raw6816step2 = -raw6816step1 := by apply Matrix.ext; change ∀ i j, raw6816step2 i j = -(raw6816step1 i j); unfold raw6816step2 raw6816step1; decide +kernel
      have hl : raw6816step2Labels = raw6816step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6816step2 raw6816step2Labels = mixedMoment B raw6816step3 raw6816step3Labels := by
      have ha : raw6816step3 = raw6816step2 := by apply Matrix.ext; unfold raw6816step3 raw6816step2; decide +kernel
      have hl : raw6816step2Labels = labelEmbedding7 ∘ raw6816step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6816step2 raw6816step2Labels raw6816step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw6817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6817step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6817step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6817step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6817step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6817 raw6817Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw6817 raw6817Labels = mixedMoment B raw6817step0 raw6817step0Labels := by
      have hz : ∀ j, raw6817 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6817step0 = (fun i j => raw6817 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6817step0 raw6817; decide +kernel
      have hl : raw6817step0Labels = raw6817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6817 raw6817Labels permutation346 hz
    mixedMoment B raw6817step0 raw6817step0Labels = mixedMoment B raw6817step1 raw6817step1Labels := by
      have ha : raw6817step1 = (fun i j => raw6817step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6817step1 raw6817step0; decide +kernel
      have hl : raw6817step1Labels = raw6817step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6817step0 raw6817step0Labels permutation97 permutation6
    mixedMoment B raw6817step1 raw6817step1Labels = mixedMoment B raw6817step2 raw6817step2Labels := by
      have ha : raw6817step2 = raw6817step1 := by apply Matrix.ext; unfold raw6817step2 raw6817step1; decide +kernel
      have hl : raw6817step1Labels = labelEmbedding9 ∘ raw6817step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6817step1 raw6817step1Labels raw6817step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw6818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6818step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6818step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6818 raw6818Labels = mixedMoment B node4568 node4568Labels := by
  calc
    mixedMoment B raw6818 raw6818Labels = mixedMoment B raw6818step0 raw6818step0Labels := by
      have hz : ∀ j, raw6818 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6818step0 = (fun i j => raw6818 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6818step0 raw6818; decide +kernel
      have hl : raw6818step0Labels = raw6818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6818 raw6818Labels permutation346 hz
    mixedMoment B raw6818step0 raw6818step0Labels = mixedMoment B raw6818step1 raw6818step1Labels := by
      have ha : raw6818step1 = (fun i j => raw6818step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6818step1 raw6818step0; decide +kernel
      have hl : raw6818step1Labels = raw6818step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6818step0 raw6818step0Labels permutation40 permutation3
    mixedMoment B raw6818step1 raw6818step1Labels = mixedMoment B raw6818step2 raw6818step2Labels := by
      have ha : raw6818step2 = raw6818step1 := by apply Matrix.ext; unfold raw6818step2 raw6818step1; decide +kernel
      have hl : raw6818step1Labels = labelEmbedding6 ∘ raw6818step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6818step1 raw6818step1Labels raw6818step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4568 node4568Labels := by rfl

def raw6819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6819step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw6819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6819 raw6819Labels = mixedMoment B node5154 node5154Labels := by
  calc
    mixedMoment B raw6819 raw6819Labels = mixedMoment B raw6819step0 raw6819step0Labels := by
      have ha : raw6819step0 = (fun i j => raw6819 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6819step0 raw6819; decide +kernel
      have hl : raw6819step0Labels = raw6819Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6819 raw6819Labels permutation182 permutation2
    _ = mixedMoment B node5154 node5154Labels := by rfl

def raw6820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -3, 2], ![0, 1, -1], ![-2, 2, 0], ![-2, 1, 1]]
def raw6820step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw6820step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6820step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw6820step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6820 raw6820Labels = mixedMoment B node5210 node5210Labels := by
  calc
    mixedMoment B raw6820 raw6820Labels = mixedMoment B raw6820step0 raw6820step0Labels := by
      have hz : ∀ j, raw6820 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6820step0 = (fun i j => raw6820 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6820step0 raw6820; decide +kernel
      have hl : raw6820step0Labels = raw6820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6820 raw6820Labels permutation346 hz
    mixedMoment B raw6820step0 raw6820step0Labels = mixedMoment B raw6820step1 raw6820step1Labels := by
      have ha : raw6820step1 = (fun i j => raw6820step0 (permutation83 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6820step1 raw6820step0; decide +kernel
      have hl : raw6820step1Labels = raw6820step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6820step0 raw6820step0Labels permutation83 permutation4
    mixedMoment B raw6820step1 raw6820step1Labels = mixedMoment B raw6820step2 raw6820step2Labels := by
      have ha : raw6820step2 = -raw6820step1 := by apply Matrix.ext; change ∀ i j, raw6820step2 i j = -(raw6820step1 i j); unfold raw6820step2 raw6820step1; decide +kernel
      have hl : raw6820step2Labels = raw6820step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6820step2 raw6820step2Labels = mixedMoment B raw6820step3 raw6820step3Labels := by
      have ha : raw6820step3 = raw6820step2 := by apply Matrix.ext; unfold raw6820step3 raw6820step2; decide +kernel
      have hl : raw6820step2Labels = labelEmbedding7 ∘ raw6820step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6820step2 raw6820step2Labels raw6820step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5210 node5210Labels := by rfl

def raw6821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw6821step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6821 raw6821Labels = mixedMoment B node5287 node5287Labels := by
  calc
    mixedMoment B raw6821 raw6821Labels = mixedMoment B raw6821step0 raw6821step0Labels := by
      have hz : ∀ j, raw6821 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6821step0 = (fun i j => raw6821 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6821step0 raw6821; decide +kernel
      have hl : raw6821step0Labels = raw6821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6821 raw6821Labels permutation346 hz
    mixedMoment B raw6821step0 raw6821step0Labels = mixedMoment B raw6821step1 raw6821step1Labels := by
      have ha : raw6821step1 = (fun i j => raw6821step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6821step1 raw6821step0; decide +kernel
      have hl : raw6821step1Labels = raw6821step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6821step0 raw6821step0Labels permutation46 permutation2
    _ = mixedMoment B node5287 node5287Labels := by rfl

def raw6822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6822step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6822 raw6822Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw6822 raw6822Labels = mixedMoment B raw6822step0 raw6822step0Labels := by
      have hz : ∀ j, raw6822 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6822step0 = (fun i j => raw6822 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6822step0 raw6822; decide +kernel
      have hl : raw6822step0Labels = raw6822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6822 raw6822Labels permutation346 hz
    mixedMoment B raw6822step0 raw6822step0Labels = mixedMoment B raw6822step1 raw6822step1Labels := by
      have ha : raw6822step1 = (fun i j => raw6822step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6822step1 raw6822step0; decide +kernel
      have hl : raw6822step1Labels = raw6822step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6822step0 raw6822step0Labels permutation39 permutation2
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw6823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6823step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6823step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6823 raw6823Labels = mixedMoment B node4561 node4561Labels := by
  calc
    mixedMoment B raw6823 raw6823Labels = mixedMoment B raw6823step0 raw6823step0Labels := by
      have ha : raw6823step0 = (fun i j => raw6823 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6823step0 raw6823; decide +kernel
      have hl : raw6823step0Labels = raw6823Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6823 raw6823Labels permutation202 permutation3
    mixedMoment B raw6823step0 raw6823step0Labels = mixedMoment B raw6823step1 raw6823step1Labels := by
      have ha : raw6823step1 = raw6823step0 := by apply Matrix.ext; unfold raw6823step1 raw6823step0; decide +kernel
      have hl : raw6823step0Labels = labelEmbedding6 ∘ raw6823step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6823step0 raw6823step0Labels raw6823step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4561 node4561Labels := by rfl

def raw6824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6824step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6824step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6824 raw6824Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw6824 raw6824Labels = mixedMoment B raw6824step0 raw6824step0Labels := by
      have ha : raw6824step0 = (fun i j => raw6824 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6824step0 raw6824; decide +kernel
      have hl : raw6824step0Labels = raw6824Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6824 raw6824Labels permutation158 permutation2
    _ = mixedMoment B node5086 node5086Labels := by rfl

def raw6825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6825step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6825 raw6825Labels = mixedMoment B node5209 node5209Labels := by
  calc
    mixedMoment B raw6825 raw6825Labels = mixedMoment B raw6825step0 raw6825step0Labels := by
      have ha : raw6825step0 = (fun i j => raw6825 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6825step0 raw6825; decide +kernel
      have hl : raw6825step0Labels = raw6825Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6825 raw6825Labels permutation200 permutation2
    _ = mixedMoment B node5209 node5209Labels := by rfl

def raw6826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6826 raw6826Labels = mixedMoment B node5254 node5254Labels := by
  calc
    mixedMoment B raw6826 raw6826Labels = mixedMoment B raw6826step0 raw6826step0Labels := by
      have ha : raw6826step0 = (fun i j => raw6826 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6826step0 raw6826; decide +kernel
      have hl : raw6826step0Labels = raw6826Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6826 raw6826Labels permutation166 permutation2
    _ = mixedMoment B node5254 node5254Labels := by rfl

def raw6827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw6827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6827 raw6827Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw6827 raw6827Labels = mixedMoment B raw6827step0 raw6827step0Labels := by
      have ha : raw6827step0 = (fun i j => raw6827 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6827step0 raw6827; decide +kernel
      have hl : raw6827step0Labels = raw6827Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6827 raw6827Labels permutation159 permutation2
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw6828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6828step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6828step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6828 raw6828Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw6828 raw6828Labels = mixedMoment B raw6828step0 raw6828step0Labels := by
      have hz : ∀ j, raw6828 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6828step0 = (fun i j => raw6828 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6828step0 raw6828; decide +kernel
      have hl : raw6828step0Labels = raw6828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6828 raw6828Labels permutation346 hz
    mixedMoment B raw6828step0 raw6828step0Labels = mixedMoment B raw6828step1 raw6828step1Labels := by
      have ha : raw6828step1 = (fun i j => raw6828step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6828step1 raw6828step0; decide +kernel
      have hl : raw6828step1Labels = raw6828step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6828step0 raw6828step0Labels permutation34 permutation2
    _ = mixedMoment B node4607 node4607Labels := by rfl

def raw6829 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6829step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6829step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6829step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6829 raw6829Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw6829 raw6829Labels = mixedMoment B raw6829step0 raw6829step0Labels := by
      have hz : ∀ j, raw6829 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6829step0 = (fun i j => raw6829 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6829step0 raw6829; decide +kernel
      have hl : raw6829step0Labels = raw6829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6829 raw6829Labels permutation346 hz
    mixedMoment B raw6829step0 raw6829step0Labels = mixedMoment B raw6829step1 raw6829step1Labels := by
      have ha : raw6829step1 = (fun i j => raw6829step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6829step1 raw6829step0; decide +kernel
      have hl : raw6829step1Labels = raw6829step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6829step0 raw6829step0Labels permutation34 permutation2
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw6830 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6830step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6830 raw6830Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw6830 raw6830Labels = mixedMoment B raw6830step0 raw6830step0Labels := by
      have ha : raw6830step0 = (fun i j => raw6830 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6830step0 raw6830; decide +kernel
      have hl : raw6830step0Labels = raw6830Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6830 raw6830Labels permutation178 permutation2
    _ = mixedMoment B node5138 node5138Labels := by rfl

def raw6831 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6831step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6831 raw6831Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw6831 raw6831Labels = mixedMoment B raw6831step0 raw6831step0Labels := by
      have hz : ∀ j, raw6831 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6831step0 = (fun i j => raw6831 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6831step0 raw6831; decide +kernel
      have hl : raw6831step0Labels = raw6831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6831 raw6831Labels permutation346 hz
    mixedMoment B raw6831step0 raw6831step0Labels = mixedMoment B raw6831step1 raw6831step1Labels := by
      have ha : raw6831step1 = (fun i j => raw6831step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6831step1 raw6831step0; decide +kernel
      have hl : raw6831step1Labels = raw6831step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6831step0 raw6831step0Labels permutation34 permutation2
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw6832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6832step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6832step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6832 raw6832Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw6832 raw6832Labels = mixedMoment B raw6832step0 raw6832step0Labels := by
      have hz : ∀ j, raw6832 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6832step0 = (fun i j => raw6832 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6832step0 raw6832; decide +kernel
      have hl : raw6832step0Labels = raw6832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6832 raw6832Labels permutation346 hz
    mixedMoment B raw6832step0 raw6832step0Labels = mixedMoment B raw6832step1 raw6832step1Labels := by
      have ha : raw6832step1 = (fun i j => raw6832step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6832step1 raw6832step0; decide +kernel
      have hl : raw6832step1Labels = raw6832step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6832step0 raw6832step0Labels permutation37 permutation2
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw6833 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6833step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6833step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6833step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6833step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6833 raw6833Labels = mixedMoment B node4565 node4565Labels := by
  calc
    mixedMoment B raw6833 raw6833Labels = mixedMoment B raw6833step0 raw6833step0Labels := by
      have hz : ∀ j, raw6833 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6833step0 = (fun i j => raw6833 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6833step0 raw6833; decide +kernel
      have hl : raw6833step0Labels = raw6833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6833 raw6833Labels permutation346 hz
    mixedMoment B raw6833step0 raw6833step0Labels = mixedMoment B raw6833step1 raw6833step1Labels := by
      have ha : raw6833step1 = (fun i j => raw6833step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6833step1 raw6833step0; decide +kernel
      have hl : raw6833step1Labels = raw6833step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6833step0 raw6833step0Labels permutation38 permutation3
    mixedMoment B raw6833step1 raw6833step1Labels = mixedMoment B raw6833step2 raw6833step2Labels := by
      have ha : raw6833step2 = raw6833step1 := by apply Matrix.ext; unfold raw6833step2 raw6833step1; decide +kernel
      have hl : raw6833step1Labels = labelEmbedding6 ∘ raw6833step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6833step1 raw6833step1Labels raw6833step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4565 node4565Labels := by rfl

def raw6834 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6834step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6834step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6834 raw6834Labels = mixedMoment B node5090 node5090Labels := by
  calc
    mixedMoment B raw6834 raw6834Labels = mixedMoment B raw6834step0 raw6834step0Labels := by
      have hz : ∀ j, raw6834 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6834step0 = (fun i j => raw6834 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6834step0 raw6834; decide +kernel
      have hl : raw6834step0Labels = raw6834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6834 raw6834Labels permutation346 hz
    mixedMoment B raw6834step0 raw6834step0Labels = mixedMoment B raw6834step1 raw6834step1Labels := by
      have ha : raw6834step1 = (fun i j => raw6834step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6834step1 raw6834step0; decide +kernel
      have hl : raw6834step1Labels = raw6834step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6834step0 raw6834step0Labels permutation33 permutation2
    _ = mixedMoment B node5090 node5090Labels := by rfl

def raw6835 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6835step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6835 raw6835Labels = mixedMoment B node5131 node5131Labels := by
  calc
    mixedMoment B raw6835 raw6835Labels = mixedMoment B raw6835step0 raw6835step0Labels := by
      have ha : raw6835step0 = (fun i j => raw6835 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6835step0 raw6835; decide +kernel
      have hl : raw6835step0Labels = raw6835Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6835 raw6835Labels permutation177 permutation2
    _ = mixedMoment B node5131 node5131Labels := by rfl

def raw6836 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6836step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw6836step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6836 raw6836Labels = mixedMoment B node5210 node5210Labels := by
  calc
    mixedMoment B raw6836 raw6836Labels = mixedMoment B raw6836step0 raw6836step0Labels := by
      have hz : ∀ j, raw6836 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6836step0 = (fun i j => raw6836 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6836step0 raw6836; decide +kernel
      have hl : raw6836step0Labels = raw6836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6836 raw6836Labels permutation346 hz
    mixedMoment B raw6836step0 raw6836step0Labels = mixedMoment B raw6836step1 raw6836step1Labels := by
      have ha : raw6836step1 = (fun i j => raw6836step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6836step1 raw6836step0; decide +kernel
      have hl : raw6836step1Labels = raw6836step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6836step0 raw6836step0Labels permutation39 permutation2
    _ = mixedMoment B node5210 node5210Labels := by rfl

def raw6837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw6837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw6837step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6837step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6837 raw6837Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw6837 raw6837Labels = mixedMoment B raw6837step0 raw6837step0Labels := by
      have hz : ∀ j, raw6837 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6837step0 = (fun i j => raw6837 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6837step0 raw6837; decide +kernel
      have hl : raw6837step0Labels = raw6837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6837 raw6837Labels permutation346 hz
    mixedMoment B raw6837step0 raw6837step0Labels = mixedMoment B raw6837step1 raw6837step1Labels := by
      have ha : raw6837step1 = (fun i j => raw6837step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6837step1 raw6837step0; decide +kernel
      have hl : raw6837step1Labels = raw6837step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6837step0 raw6837step0Labels permutation33 permutation2
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw6838 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6838step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6838step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw6838step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6838step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw6838step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6838 raw6838Labels = mixedMoment B node4562 node4562Labels := by
  calc
    mixedMoment B raw6838 raw6838Labels = mixedMoment B raw6838step0 raw6838step0Labels := by
      have hz : ∀ j, raw6838 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6838step0 = (fun i j => raw6838 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6838step0 raw6838; decide +kernel
      have hl : raw6838step0Labels = raw6838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6838 raw6838Labels permutation346 hz
    mixedMoment B raw6838step0 raw6838step0Labels = mixedMoment B raw6838step1 raw6838step1Labels := by
      have ha : raw6838step1 = (fun i j => raw6838step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6838step1 raw6838step0; decide +kernel
      have hl : raw6838step1Labels = raw6838step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6838step0 raw6838step0Labels permutation38 permutation3
    mixedMoment B raw6838step1 raw6838step1Labels = mixedMoment B raw6838step2 raw6838step2Labels := by
      have ha : raw6838step2 = raw6838step1 := by apply Matrix.ext; unfold raw6838step2 raw6838step1; decide +kernel
      have hl : raw6838step1Labels = labelEmbedding6 ∘ raw6838step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6838step1 raw6838step1Labels raw6838step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4562 node4562Labels := by rfl

def raw6839 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6839Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6839step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw6839step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6839step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6839step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6839step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6839step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6839 raw6839Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw6839 raw6839Labels = mixedMoment B raw6839step0 raw6839step0Labels := by
      have hz : ∀ j, raw6839 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6839step0 = (fun i j => raw6839 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6839step0 raw6839; decide +kernel
      have hl : raw6839step0Labels = raw6839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6839 raw6839Labels permutation346 hz
    mixedMoment B raw6839step0 raw6839step0Labels = mixedMoment B raw6839step1 raw6839step1Labels := by
      have ha : raw6839step1 = (fun i j => raw6839step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6839step1 raw6839step0; decide +kernel
      have hl : raw6839step1Labels = raw6839step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6839step0 raw6839step0Labels permutation151 permutation3
    mixedMoment B raw6839step1 raw6839step1Labels = mixedMoment B raw6839step2 raw6839step2Labels := by
      have ha : raw6839step2 = -raw6839step1 := by apply Matrix.ext; change ∀ i j, raw6839step2 i j = -(raw6839step1 i j); unfold raw6839step2 raw6839step1; decide +kernel
      have hl : raw6839step2Labels = raw6839step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6839step2 raw6839step2Labels = mixedMoment B raw6839step3 raw6839step3Labels := by
      have ha : raw6839step3 = raw6839step2 := by apply Matrix.ext; unfold raw6839step3 raw6839step2; decide +kernel
      have hl : raw6839step2Labels = labelEmbedding6 ∘ raw6839step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6839step2 raw6839step2Labels raw6839step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4817 node4817Labels := by rfl

def raw6840 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw6840step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6840step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw6840step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6840step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw6840step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6840 raw6840Labels = mixedMoment B node4783 node4783Labels := by
  calc
    mixedMoment B raw6840 raw6840Labels = mixedMoment B raw6840step0 raw6840step0Labels := by
      have ha : raw6840step0 = (fun i j => raw6840 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6840step0 raw6840; decide +kernel
      have hl : raw6840step0Labels = raw6840Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6840 raw6840Labels permutation676 permutation3
    mixedMoment B raw6840step0 raw6840step0Labels = mixedMoment B raw6840step1 raw6840step1Labels := by
      have ha : raw6840step1 = -raw6840step0 := by apply Matrix.ext; change ∀ i j, raw6840step1 i j = -(raw6840step0 i j); unfold raw6840step1 raw6840step0; decide +kernel
      have hl : raw6840step1Labels = raw6840step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6840step1 raw6840step1Labels = mixedMoment B raw6840step2 raw6840step2Labels := by
      have ha : raw6840step2 = raw6840step1 := by apply Matrix.ext; unfold raw6840step2 raw6840step1; decide +kernel
      have hl : raw6840step1Labels = labelEmbedding6 ∘ raw6840step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6840step1 raw6840step1Labels raw6840step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4783 node4783Labels := by rfl

def raw6841 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6841Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6841step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw6841step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6841step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw6841step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6841step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw6841step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6841 raw6841Labels = mixedMoment B node4789 node4789Labels := by
  calc
    mixedMoment B raw6841 raw6841Labels = mixedMoment B raw6841step0 raw6841step0Labels := by
      have hz : ∀ j, raw6841 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6841step0 = (fun i j => raw6841 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6841step0 raw6841; decide +kernel
      have hl : raw6841step0Labels = raw6841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6841 raw6841Labels permutation346 hz
    mixedMoment B raw6841step0 raw6841step0Labels = mixedMoment B raw6841step1 raw6841step1Labels := by
      have ha : raw6841step1 = (fun i j => raw6841step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6841step1 raw6841step0; decide +kernel
      have hl : raw6841step1Labels = raw6841step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6841step0 raw6841step0Labels permutation149 permutation3
    mixedMoment B raw6841step1 raw6841step1Labels = mixedMoment B raw6841step2 raw6841step2Labels := by
      have ha : raw6841step2 = -raw6841step1 := by apply Matrix.ext; change ∀ i j, raw6841step2 i j = -(raw6841step1 i j); unfold raw6841step2 raw6841step1; decide +kernel
      have hl : raw6841step2Labels = raw6841step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6841step2 raw6841step2Labels = mixedMoment B raw6841step3 raw6841step3Labels := by
      have ha : raw6841step3 = raw6841step2 := by apply Matrix.ext; unfold raw6841step3 raw6841step2; decide +kernel
      have hl : raw6841step2Labels = labelEmbedding6 ∘ raw6841step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6841step2 raw6841step2Labels raw6841step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4789 node4789Labels := by rfl

def raw6842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw6842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw6842step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw6842step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6842step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw6842step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6842 raw6842Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw6842 raw6842Labels = mixedMoment B raw6842step0 raw6842step0Labels := by
      have hz : ∀ j, raw6842 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6842step0 = (fun i j => raw6842 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6842step0 raw6842; decide +kernel
      have hl : raw6842step0Labels = raw6842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6842 raw6842Labels permutation346 hz
    mixedMoment B raw6842step0 raw6842step0Labels = mixedMoment B raw6842step1 raw6842step1Labels := by
      have ha : raw6842step1 = (fun i j => raw6842step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6842step1 raw6842step0; decide +kernel
      have hl : raw6842step1Labels = raw6842step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6842step0 raw6842step0Labels permutation138 permutation5
    mixedMoment B raw6842step1 raw6842step1Labels = mixedMoment B raw6842step2 raw6842step2Labels := by
      have ha : raw6842step2 = raw6842step1 := by apply Matrix.ext; unfold raw6842step2 raw6842step1; decide +kernel
      have hl : raw6842step1Labels = labelEmbedding8 ∘ raw6842step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6842step1 raw6842step1Labels raw6842step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4836 node4836Labels := by rfl

def raw6843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6843step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw6843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6843step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6843step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6843 raw6843Labels = mixedMoment B node3856 node3856Labels := by
  calc
    mixedMoment B raw6843 raw6843Labels = mixedMoment B raw6843step0 raw6843step0Labels := by
      have hz : ∀ j, raw6843 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6843step0 = (fun i j => raw6843 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6843step0 raw6843; decide +kernel
      have hl : raw6843step0Labels = raw6843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6843 raw6843Labels permutation346 hz
    mixedMoment B raw6843step0 raw6843step0Labels = mixedMoment B raw6843step1 raw6843step1Labels := by
      have ha : raw6843step1 = (fun i j => raw6843step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6843step1 raw6843step0; decide +kernel
      have hl : raw6843step1Labels = raw6843step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6843step0 raw6843step0Labels permutation151 permutation3
    mixedMoment B raw6843step1 raw6843step1Labels = mixedMoment B raw6843step2 raw6843step2Labels := by
      have ha : raw6843step2 = -raw6843step1 := by apply Matrix.ext; change ∀ i j, raw6843step2 i j = -(raw6843step1 i j); unfold raw6843step2 raw6843step1; decide +kernel
      have hl : raw6843step2Labels = raw6843step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3856 node3856Labels := by rfl

def raw6844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6844Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6844step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6844step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6844step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6844 raw6844Labels = mixedMoment B node3841 node3841Labels := by
  calc
    mixedMoment B raw6844 raw6844Labels = mixedMoment B raw6844step0 raw6844step0Labels := by
      have ha : raw6844step0 = (fun i j => raw6844 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6844step0 raw6844; decide +kernel
      have hl : raw6844step0Labels = raw6844Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6844 raw6844Labels permutation676 permutation3
    mixedMoment B raw6844step0 raw6844step0Labels = mixedMoment B raw6844step1 raw6844step1Labels := by
      have ha : raw6844step1 = -raw6844step0 := by apply Matrix.ext; change ∀ i j, raw6844step1 i j = -(raw6844step0 i j); unfold raw6844step1 raw6844step0; decide +kernel
      have hl : raw6844step1Labels = raw6844step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3841 node3841Labels := by rfl

def raw6845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6845Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6845step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6845step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6845 raw6845Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw6845 raw6845Labels = mixedMoment B raw6845step0 raw6845step0Labels := by
      have hz : ∀ j, raw6845 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6845step0 = (fun i j => raw6845 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6845step0 raw6845; decide +kernel
      have hl : raw6845step0Labels = raw6845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6845 raw6845Labels permutation346 hz
    mixedMoment B raw6845step0 raw6845step0Labels = mixedMoment B raw6845step1 raw6845step1Labels := by
      have ha : raw6845step1 = (fun i j => raw6845step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6845step1 raw6845step0; decide +kernel
      have hl : raw6845step1Labels = raw6845step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6845step0 raw6845step0Labels permutation97 permutation6
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw6846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6846Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6846step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6846step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6846 raw6846Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw6846 raw6846Labels = mixedMoment B raw6846step0 raw6846step0Labels := by
      have hz : ∀ j, raw6846 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6846step0 = (fun i j => raw6846 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6846step0 raw6846; decide +kernel
      have hl : raw6846step0Labels = raw6846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6846 raw6846Labels permutation346 hz
    mixedMoment B raw6846step0 raw6846step0Labels = mixedMoment B raw6846step1 raw6846step1Labels := by
      have ha : raw6846step1 = (fun i j => raw6846step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6846step1 raw6846step0; decide +kernel
      have hl : raw6846step1Labels = raw6846step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6846step0 raw6846step0Labels permutation97 permutation6
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw6847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6847Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6847step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6847step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6847 raw6847Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw6847 raw6847Labels = mixedMoment B raw6847step0 raw6847step0Labels := by
      have hz : ∀ j, raw6847 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6847step0 = (fun i j => raw6847 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6847step0 raw6847; decide +kernel
      have hl : raw6847step0Labels = raw6847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6847 raw6847Labels permutation346 hz
    mixedMoment B raw6847step0 raw6847step0Labels = mixedMoment B raw6847step1 raw6847step1Labels := by
      have ha : raw6847step1 = (fun i j => raw6847step0 (permutation97 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6847step1 raw6847step0; decide +kernel
      have hl : raw6847step1Labels = raw6847step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6847step0 raw6847step0Labels permutation97 permutation6
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw6848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6848Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6848step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6848step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6848 raw6848Labels = mixedMoment B node1185 node1185Labels := by
  calc
    mixedMoment B raw6848 raw6848Labels = mixedMoment B raw6848step0 raw6848step0Labels := by
      have hz : ∀ j, raw6848 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6848step0 = (fun i j => raw6848 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6848step0 raw6848; decide +kernel
      have hl : raw6848step0Labels = raw6848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6848 raw6848Labels permutation346 hz
    mixedMoment B raw6848step0 raw6848step0Labels = mixedMoment B raw6848step1 raw6848step1Labels := by
      have ha : raw6848step1 = (fun i j => raw6848step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6848step1 raw6848step0; decide +kernel
      have hl : raw6848step1Labels = raw6848step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6848step0 raw6848step0Labels permutation40 permutation3
    _ = mixedMoment B node1185 node1185Labels := by rfl

def raw6849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6849Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6849step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6849step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6849 raw6849Labels = mixedMoment B node2907 node2907Labels := by
  calc
    mixedMoment B raw6849 raw6849Labels = mixedMoment B raw6849step0 raw6849step0Labels := by
      have ha : raw6849step0 = (fun i j => raw6849 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6849step0 raw6849; decide +kernel
      have hl : raw6849step0Labels = raw6849Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6849 raw6849Labels permutation184 permutation3
    _ = mixedMoment B node2907 node2907Labels := by rfl

def raw6850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6850Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6850step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6850step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6850 raw6850Labels = mixedMoment B node2838 node2838Labels := by
  calc
    mixedMoment B raw6850 raw6850Labels = mixedMoment B raw6850step0 raw6850step0Labels := by
      have hz : ∀ j, raw6850 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6850step0 = (fun i j => raw6850 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6850step0 raw6850; decide +kernel
      have hl : raw6850step0Labels = raw6850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6850 raw6850Labels permutation346 hz
    mixedMoment B raw6850step0 raw6850step0Labels = mixedMoment B raw6850step1 raw6850step1Labels := by
      have ha : raw6850step1 = (fun i j => raw6850step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6850step1 raw6850step0; decide +kernel
      have hl : raw6850step1Labels = raw6850step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6850step0 raw6850step0Labels permutation40 permutation3
    _ = mixedMoment B node2838 node2838Labels := by rfl

def raw6851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6851Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6851step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6851step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw6851step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6851 raw6851Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw6851 raw6851Labels = mixedMoment B raw6851step0 raw6851step0Labels := by
      have hz : ∀ j, raw6851 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6851step0 = (fun i j => raw6851 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6851step0 raw6851; decide +kernel
      have hl : raw6851step0Labels = raw6851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6851 raw6851Labels permutation346 hz
    mixedMoment B raw6851step0 raw6851step0Labels = mixedMoment B raw6851step1 raw6851step1Labels := by
      have ha : raw6851step1 = (fun i j => raw6851step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6851step1 raw6851step0; decide +kernel
      have hl : raw6851step1Labels = raw6851step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6851step0 raw6851step0Labels permutation40 permutation3
    _ = mixedMoment B node3025 node3025Labels := by rfl

def raw6852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6852Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6852step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6852step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6852 raw6852Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw6852 raw6852Labels = mixedMoment B raw6852step0 raw6852step0Labels := by
      have hz : ∀ j, raw6852 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6852step0 = (fun i j => raw6852 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6852step0 raw6852; decide +kernel
      have hl : raw6852step0Labels = raw6852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6852 raw6852Labels permutation346 hz
    mixedMoment B raw6852step0 raw6852step0Labels = mixedMoment B raw6852step1 raw6852step1Labels := by
      have ha : raw6852step1 = (fun i j => raw6852step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6852step1 raw6852step0; decide +kernel
      have hl : raw6852step1Labels = raw6852step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6852step0 raw6852step0Labels permutation41 permutation3
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw6853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6853Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6853step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6853 raw6853Labels = mixedMoment B node1178 node1178Labels := by
  calc
    mixedMoment B raw6853 raw6853Labels = mixedMoment B raw6853step0 raw6853step0Labels := by
      have ha : raw6853step0 = (fun i j => raw6853 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6853step0 raw6853; decide +kernel
      have hl : raw6853step0Labels = raw6853Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6853 raw6853Labels permutation202 permutation3
    _ = mixedMoment B node1178 node1178Labels := by rfl

def raw6854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6854Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6854step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6854step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6854 raw6854Labels = mixedMoment B node2974 node2974Labels := by
  calc
    mixedMoment B raw6854 raw6854Labels = mixedMoment B raw6854step0 raw6854step0Labels := by
      have ha : raw6854step0 = (fun i j => raw6854 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6854step0 raw6854; decide +kernel
      have hl : raw6854step0Labels = raw6854Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6854 raw6854Labels permutation160 permutation3
    _ = mixedMoment B node2974 node2974Labels := by rfl

def raw6855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6855Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6855step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6855 raw6855Labels = mixedMoment B node2833 node2833Labels := by
  calc
    mixedMoment B raw6855 raw6855Labels = mixedMoment B raw6855step0 raw6855step0Labels := by
      have ha : raw6855step0 = (fun i j => raw6855 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6855step0 raw6855; decide +kernel
      have hl : raw6855step0Labels = raw6855Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6855 raw6855Labels permutation202 permutation3
    _ = mixedMoment B node2833 node2833Labels := by rfl

def raw6856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6856Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw6856step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6856 raw6856Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw6856 raw6856Labels = mixedMoment B raw6856step0 raw6856step0Labels := by
      have ha : raw6856step0 = (fun i j => raw6856 (permutation212 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6856step0 raw6856; decide +kernel
      have hl : raw6856step0Labels = raw6856Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6856 raw6856Labels permutation212 permutation3
    _ = mixedMoment B node3016 node3016Labels := by rfl

def raw6857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6857Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw6857step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6857 raw6857Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw6857 raw6857Labels = mixedMoment B raw6857step0 raw6857step0Labels := by
      have ha : raw6857step0 = (fun i j => raw6857 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6857step0 raw6857; decide +kernel
      have hl : raw6857step0Labels = raw6857Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6857 raw6857Labels permutation202 permutation3
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw6858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6858Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6858step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6858step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6858 raw6858Labels = mixedMoment B node1261 node1261Labels := by
  calc
    mixedMoment B raw6858 raw6858Labels = mixedMoment B raw6858step0 raw6858step0Labels := by
      have hz : ∀ j, raw6858 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6858step0 = (fun i j => raw6858 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6858step0 raw6858; decide +kernel
      have hl : raw6858step0Labels = raw6858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6858 raw6858Labels permutation346 hz
    mixedMoment B raw6858step0 raw6858step0Labels = mixedMoment B raw6858step1 raw6858step1Labels := by
      have ha : raw6858step1 = (fun i j => raw6858step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6858step1 raw6858step0; decide +kernel
      have hl : raw6858step1Labels = raw6858step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6858step0 raw6858step0Labels permutation32 permutation3
    _ = mixedMoment B node1261 node1261Labels := by rfl

def raw6859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6859Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6859step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6859step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6859step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6859 raw6859Labels = mixedMoment B node2997 node2997Labels := by
  calc
    mixedMoment B raw6859 raw6859Labels = mixedMoment B raw6859step0 raw6859step0Labels := by
      have hz : ∀ j, raw6859 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6859step0 = (fun i j => raw6859 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6859step0 raw6859; decide +kernel
      have hl : raw6859step0Labels = raw6859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6859 raw6859Labels permutation346 hz
    mixedMoment B raw6859step0 raw6859step0Labels = mixedMoment B raw6859step1 raw6859step1Labels := by
      have ha : raw6859step1 = (fun i j => raw6859step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6859step1 raw6859step0; decide +kernel
      have hl : raw6859step1Labels = raw6859step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6859step0 raw6859step0Labels permutation32 permutation3
    _ = mixedMoment B node2997 node2997Labels := by rfl

def raw6860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6860Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6860step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6860 raw6860Labels = mixedMoment B node2933 node2933Labels := by
  calc
    mixedMoment B raw6860 raw6860Labels = mixedMoment B raw6860step0 raw6860step0Labels := by
      have ha : raw6860step0 = (fun i j => raw6860 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6860step0 raw6860; decide +kernel
      have hl : raw6860step0Labels = raw6860Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6860 raw6860Labels permutation176 permutation3
    _ = mixedMoment B node2933 node2933Labels := by rfl

def raw6861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6861Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6861step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6861step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6861 raw6861Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw6861 raw6861Labels = mixedMoment B raw6861step0 raw6861step0Labels := by
      have hz : ∀ j, raw6861 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6861step0 = (fun i j => raw6861 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6861step0 raw6861; decide +kernel
      have hl : raw6861step0Labels = raw6861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6861 raw6861Labels permutation346 hz
    mixedMoment B raw6861step0 raw6861step0Labels = mixedMoment B raw6861step1 raw6861step1Labels := by
      have ha : raw6861step1 = (fun i j => raw6861step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6861step1 raw6861step0; decide +kernel
      have hl : raw6861step1Labels = raw6861step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6861step0 raw6861step0Labels permutation44 permutation3
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw6862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6862Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6862step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6862step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6862step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6862 raw6862Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw6862 raw6862Labels = mixedMoment B raw6862step0 raw6862step0Labels := by
      have hz : ∀ j, raw6862 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6862step0 = (fun i j => raw6862 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6862step0 raw6862; decide +kernel
      have hl : raw6862step0Labels = raw6862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6862 raw6862Labels permutation346 hz
    mixedMoment B raw6862step0 raw6862step0Labels = mixedMoment B raw6862step1 raw6862step1Labels := by
      have ha : raw6862step1 = (fun i j => raw6862step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6862step1 raw6862step0; decide +kernel
      have hl : raw6862step1Labels = raw6862step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6862step0 raw6862step0Labels permutation32 permutation3
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw6863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6863Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6863step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6863step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6863 raw6863Labels = mixedMoment B node1182 node1182Labels := by
  calc
    mixedMoment B raw6863 raw6863Labels = mixedMoment B raw6863step0 raw6863step0Labels := by
      have hz : ∀ j, raw6863 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6863step0 = (fun i j => raw6863 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6863step0 raw6863; decide +kernel
      have hl : raw6863step0Labels = raw6863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6863 raw6863Labels permutation346 hz
    mixedMoment B raw6863step0 raw6863step0Labels = mixedMoment B raw6863step1 raw6863step1Labels := by
      have ha : raw6863step1 = (fun i j => raw6863step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6863step1 raw6863step0; decide +kernel
      have hl : raw6863step1Labels = raw6863step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6863step0 raw6863step0Labels permutation38 permutation3
    _ = mixedMoment B node1182 node1182Labels := by rfl

def raw6864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6864Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6864step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw6864step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6864 raw6864Labels = mixedMoment B node2979 node2979Labels := by
  calc
    mixedMoment B raw6864 raw6864Labels = mixedMoment B raw6864step0 raw6864step0Labels := by
      have hz : ∀ j, raw6864 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6864step0 = (fun i j => raw6864 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6864step0 raw6864; decide +kernel
      have hl : raw6864step0Labels = raw6864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6864 raw6864Labels permutation346 hz
    mixedMoment B raw6864step0 raw6864step0Labels = mixedMoment B raw6864step1 raw6864step1Labels := by
      have ha : raw6864step1 = (fun i j => raw6864step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6864step1 raw6864step0; decide +kernel
      have hl : raw6864step1Labels = raw6864step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6864step0 raw6864step0Labels permutation32 permutation3
    _ = mixedMoment B node2979 node2979Labels := by rfl

def raw6865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6865Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6865step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6865 raw6865Labels = mixedMoment B node2905 node2905Labels := by
  calc
    mixedMoment B raw6865 raw6865Labels = mixedMoment B raw6865step0 raw6865step0Labels := by
      have ha : raw6865step0 = (fun i j => raw6865 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6865step0 raw6865; decide +kernel
      have hl : raw6865step0Labels = raw6865Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6865 raw6865Labels permutation182 permutation3
    _ = mixedMoment B node2905 node2905Labels := by rfl

def raw6866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6866Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6866step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6866step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6866 raw6866Labels = mixedMoment B node2835 node2835Labels := by
  calc
    mixedMoment B raw6866 raw6866Labels = mixedMoment B raw6866step0 raw6866step0Labels := by
      have hz : ∀ j, raw6866 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6866step0 = (fun i j => raw6866 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6866step0 raw6866; decide +kernel
      have hl : raw6866step0Labels = raw6866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6866 raw6866Labels permutation346 hz
    mixedMoment B raw6866step0 raw6866step0Labels = mixedMoment B raw6866step1 raw6866step1Labels := by
      have ha : raw6866step1 = (fun i j => raw6866step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6866step1 raw6866step0; decide +kernel
      have hl : raw6866step1Labels = raw6866step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6866step0 raw6866step0Labels permutation38 permutation3
    _ = mixedMoment B node2835 node2835Labels := by rfl

def raw6867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw6867Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw6867step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6867 raw6867Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw6867 raw6867Labels = mixedMoment B raw6867step0 raw6867step0Labels := by
      have hz : ∀ j, raw6867 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6867step0 = (fun i j => raw6867 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6867step0 raw6867; decide +kernel
      have hl : raw6867step0Labels = raw6867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6867 raw6867Labels permutation346 hz
    mixedMoment B raw6867step0 raw6867step0Labels = mixedMoment B raw6867step1 raw6867step1Labels := by
      have ha : raw6867step1 = (fun i j => raw6867step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6867step1 raw6867step0; decide +kernel
      have hl : raw6867step1Labels = raw6867step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6867step0 raw6867step0Labels permutation39 permutation3
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw6868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6868Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6868step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw6868step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6868 raw6868Labels = mixedMoment B node1179 node1179Labels := by
  calc
    mixedMoment B raw6868 raw6868Labels = mixedMoment B raw6868step0 raw6868step0Labels := by
      have hz : ∀ j, raw6868 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6868step0 = (fun i j => raw6868 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6868step0 raw6868; decide +kernel
      have hl : raw6868step0Labels = raw6868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6868 raw6868Labels permutation346 hz
    mixedMoment B raw6868step0 raw6868step0Labels = mixedMoment B raw6868step1 raw6868step1Labels := by
      have ha : raw6868step1 = (fun i j => raw6868step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6868step1 raw6868step0; decide +kernel
      have hl : raw6868step1Labels = raw6868step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6868step0 raw6868step0Labels permutation38 permutation3
    _ = mixedMoment B node1179 node1179Labels := by rfl

def raw6869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6869Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6869step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw6869step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6869step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6869step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6869 raw6869Labels = mixedMoment B node2035 node2035Labels := by
  calc
    mixedMoment B raw6869 raw6869Labels = mixedMoment B raw6869step0 raw6869step0Labels := by
      have hz : ∀ j, raw6869 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6869step0 = (fun i j => raw6869 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6869step0 raw6869; decide +kernel
      have hl : raw6869step0Labels = raw6869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6869 raw6869Labels permutation346 hz
    mixedMoment B raw6869step0 raw6869step0Labels = mixedMoment B raw6869step1 raw6869step1Labels := by
      have ha : raw6869step1 = (fun i j => raw6869step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6869step1 raw6869step0; decide +kernel
      have hl : raw6869step1Labels = raw6869step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6869step0 raw6869step0Labels permutation151 permutation3
    mixedMoment B raw6869step1 raw6869step1Labels = mixedMoment B raw6869step2 raw6869step2Labels := by
      have ha : raw6869step2 = -raw6869step1 := by apply Matrix.ext; change ∀ i j, raw6869step2 i j = -(raw6869step1 i j); unfold raw6869step2 raw6869step1; decide +kernel
      have hl : raw6869step2Labels = raw6869step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2035 node2035Labels := by rfl

def raw6870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6870Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw6870step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6870step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw6870step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6870 raw6870Labels = mixedMoment B node1992 node1992Labels := by
  calc
    mixedMoment B raw6870 raw6870Labels = mixedMoment B raw6870step0 raw6870step0Labels := by
      have ha : raw6870step0 = (fun i j => raw6870 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6870step0 raw6870; decide +kernel
      have hl : raw6870step0Labels = raw6870Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6870 raw6870Labels permutation676 permutation3
    mixedMoment B raw6870step0 raw6870step0Labels = mixedMoment B raw6870step1 raw6870step1Labels := by
      have ha : raw6870step1 = -raw6870step0 := by apply Matrix.ext; change ∀ i j, raw6870step1 i j = -(raw6870step0 i j); unfold raw6870step1 raw6870step0; decide +kernel
      have hl : raw6870step1Labels = raw6870step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1992 node1992Labels := by rfl

def raw6871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6871Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6871step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-3, 2, 1]]
def raw6871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6871step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw6871step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6871 raw6871Labels = mixedMoment B node2004 node2004Labels := by
  calc
    mixedMoment B raw6871 raw6871Labels = mixedMoment B raw6871step0 raw6871step0Labels := by
      have hz : ∀ j, raw6871 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6871step0 = (fun i j => raw6871 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6871step0 raw6871; decide +kernel
      have hl : raw6871step0Labels = raw6871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6871 raw6871Labels permutation346 hz
    mixedMoment B raw6871step0 raw6871step0Labels = mixedMoment B raw6871step1 raw6871step1Labels := by
      have ha : raw6871step1 = (fun i j => raw6871step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6871step1 raw6871step0; decide +kernel
      have hl : raw6871step1Labels = raw6871step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6871step0 raw6871step0Labels permutation149 permutation3
    mixedMoment B raw6871step1 raw6871step1Labels = mixedMoment B raw6871step2 raw6871step2Labels := by
      have ha : raw6871step2 = -raw6871step1 := by apply Matrix.ext; change ∀ i j, raw6871step2 i j = -(raw6871step1 i j); unfold raw6871step2 raw6871step1; decide +kernel
      have hl : raw6871step2Labels = raw6871step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2004 node2004Labels := by rfl

def raw6872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw6872Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6872step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw6872step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6872step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw6872step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6872step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw6872step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6872 raw6872Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw6872 raw6872Labels = mixedMoment B raw6872step0 raw6872step0Labels := by
      have hz : ∀ j, raw6872 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6872step0 = (fun i j => raw6872 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6872step0 raw6872; decide +kernel
      have hl : raw6872step0Labels = raw6872Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6872 raw6872Labels permutation346 hz
    mixedMoment B raw6872step0 raw6872step0Labels = mixedMoment B raw6872step1 raw6872step1Labels := by
      have ha : raw6872step1 = (fun i j => raw6872step0 (permutation139 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6872step1 raw6872step0; decide +kernel
      have hl : raw6872step1Labels = raw6872step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6872step0 raw6872step0Labels permutation139 permutation3
    mixedMoment B raw6872step1 raw6872step1Labels = mixedMoment B raw6872step2 raw6872step2Labels := by
      have ha : raw6872step2 = -raw6872step1 := by apply Matrix.ext; change ∀ i j, raw6872step2 i j = -(raw6872step1 i j); unfold raw6872step2 raw6872step1; decide +kernel
      have hl : raw6872step2Labels = raw6872step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2197 node2197Labels := by rfl

def raw6873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6873Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6873step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6873step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6873step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6873step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6873step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6873 raw6873Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw6873 raw6873Labels = mixedMoment B raw6873step0 raw6873step0Labels := by
      have hz : ∀ j, raw6873 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6873step0 = (fun i j => raw6873 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6873step0 raw6873; decide +kernel
      have hl : raw6873step0Labels = raw6873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6873 raw6873Labels permutation346 hz
    mixedMoment B raw6873step0 raw6873step0Labels = mixedMoment B raw6873step1 raw6873step1Labels := by
      have ha : raw6873step1 = (fun i j => raw6873step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6873step1 raw6873step0; decide +kernel
      have hl : raw6873step1Labels = raw6873step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6873step0 raw6873step0Labels permutation37 permutation7
    mixedMoment B raw6873step1 raw6873step1Labels = mixedMoment B raw6873step2 raw6873step2Labels := by
      have ha : raw6873step2 = -raw6873step1 := by apply Matrix.ext; change ∀ i j, raw6873step2 i j = -(raw6873step1 i j); unfold raw6873step2 raw6873step1; decide +kernel
      have hl : raw6873step2Labels = raw6873step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6873step2 raw6873step2Labels = mixedMoment B raw6873step3 raw6873step3Labels := by
      have ha : raw6873step3 = raw6873step2 := by apply Matrix.ext; unfold raw6873step3 raw6873step2; decide +kernel
      have hl : raw6873step2Labels = labelEmbedding1 ∘ raw6873step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6873step2 raw6873step2Labels raw6873step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw6874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6874Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6874step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6874 raw6874Labels = mixedMoment B node3841 node3841Labels := by
  calc
    mixedMoment B raw6874 raw6874Labels = mixedMoment B raw6874step0 raw6874step0Labels := by
      have ha : raw6874step0 = (fun i j => raw6874 (permutation617 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6874step0 raw6874; decide +kernel
      have hl : raw6874step0Labels = raw6874Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6874 raw6874Labels permutation617 permutation5
    mixedMoment B raw6874step0 raw6874step0Labels = mixedMoment B raw6874step1 raw6874step1Labels := by
      have ha : raw6874step1 = raw6874step0 := by apply Matrix.ext; unfold raw6874step1 raw6874step0; decide +kernel
      have hl : raw6874step0Labels = labelEmbedding1 ∘ raw6874step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6874step0 raw6874step0Labels raw6874step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3841 node3841Labels := by rfl

def raw6875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6875Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6875step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw6875step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6875step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6875step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6875step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6875step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6875 raw6875Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw6875 raw6875Labels = mixedMoment B raw6875step0 raw6875step0Labels := by
      have hz : ∀ j, raw6875 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6875step0 = (fun i j => raw6875 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6875step0 raw6875; decide +kernel
      have hl : raw6875step0Labels = raw6875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6875 raw6875Labels permutation346 hz
    mixedMoment B raw6875step0 raw6875step0Labels = mixedMoment B raw6875step1 raw6875step1Labels := by
      have ha : raw6875step1 = (fun i j => raw6875step0 (permutation82 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6875step1 raw6875step0; decide +kernel
      have hl : raw6875step1Labels = raw6875step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6875step0 raw6875step0Labels permutation82 permutation5
    mixedMoment B raw6875step1 raw6875step1Labels = mixedMoment B raw6875step2 raw6875step2Labels := by
      have ha : raw6875step2 = -raw6875step1 := by apply Matrix.ext; change ∀ i j, raw6875step2 i j = -(raw6875step1 i j); unfold raw6875step2 raw6875step1; decide +kernel
      have hl : raw6875step2Labels = raw6875step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6875step2 raw6875step2Labels = mixedMoment B raw6875step3 raw6875step3Labels := by
      have ha : raw6875step3 = raw6875step2 := by apply Matrix.ext; unfold raw6875step3 raw6875step2; decide +kernel
      have hl : raw6875step2Labels = labelEmbedding1 ∘ raw6875step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6875step2 raw6875step2Labels raw6875step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw6876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6876Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6876step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6876step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6876step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6876step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6876step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6876step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6876 raw6876Labels = mixedMoment B node3856 node3856Labels := by
  calc
    mixedMoment B raw6876 raw6876Labels = mixedMoment B raw6876step0 raw6876step0Labels := by
      have hz : ∀ j, raw6876 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6876step0 = (fun i j => raw6876 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6876step0 raw6876; decide +kernel
      have hl : raw6876step0Labels = raw6876Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6876 raw6876Labels permutation346 hz
    mixedMoment B raw6876step0 raw6876step0Labels = mixedMoment B raw6876step1 raw6876step1Labels := by
      have ha : raw6876step1 = (fun i j => raw6876step0 (permutation135 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6876step1 raw6876step0; decide +kernel
      have hl : raw6876step1Labels = raw6876step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6876step0 raw6876step0Labels permutation135 permutation5
    mixedMoment B raw6876step1 raw6876step1Labels = mixedMoment B raw6876step2 raw6876step2Labels := by
      have ha : raw6876step2 = raw6876step1 := by apply Matrix.ext; unfold raw6876step2 raw6876step1; decide +kernel
      have hl : raw6876step1Labels = labelEmbedding1 ∘ raw6876step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6876step1 raw6876step1Labels raw6876step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3856 node3856Labels := by rfl

def raw6877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6877Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6877step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw6877step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6877step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6877step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6877step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6877step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6877 raw6877Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw6877 raw6877Labels = mixedMoment B raw6877step0 raw6877step0Labels := by
      have hz : ∀ j, raw6877 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6877step0 = (fun i j => raw6877 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6877step0 raw6877; decide +kernel
      have hl : raw6877step0Labels = raw6877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6877 raw6877Labels permutation346 hz
    mixedMoment B raw6877step0 raw6877step0Labels = mixedMoment B raw6877step1 raw6877step1Labels := by
      have ha : raw6877step1 = (fun i j => raw6877step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6877step1 raw6877step0; decide +kernel
      have hl : raw6877step1Labels = raw6877step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6877step0 raw6877step0Labels permutation37 permutation7
    mixedMoment B raw6877step1 raw6877step1Labels = mixedMoment B raw6877step2 raw6877step2Labels := by
      have ha : raw6877step2 = -raw6877step1 := by apply Matrix.ext; change ∀ i j, raw6877step2 i j = -(raw6877step1 i j); unfold raw6877step2 raw6877step1; decide +kernel
      have hl : raw6877step2Labels = raw6877step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6877step2 raw6877step2Labels = mixedMoment B raw6877step3 raw6877step3Labels := by
      have ha : raw6877step3 = raw6877step2 := by apply Matrix.ext; unfold raw6877step3 raw6877step2; decide +kernel
      have hl : raw6877step2Labels = labelEmbedding1 ∘ raw6877step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6877step2 raw6877step2Labels raw6877step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw6878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6878Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6878step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw6878step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6878step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6878step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6878step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6878step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6878 raw6878Labels = mixedMoment B node3240 node3240Labels := by
  calc
    mixedMoment B raw6878 raw6878Labels = mixedMoment B raw6878step0 raw6878step0Labels := by
      have hz : ∀ j, raw6878 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6878step0 = (fun i j => raw6878 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6878step0 raw6878; decide +kernel
      have hl : raw6878step0Labels = raw6878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6878 raw6878Labels permutation346 hz
    mixedMoment B raw6878step0 raw6878step0Labels = mixedMoment B raw6878step1 raw6878step1Labels := by
      have ha : raw6878step1 = (fun i j => raw6878step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6878step1 raw6878step0; decide +kernel
      have hl : raw6878step1Labels = raw6878step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6878step0 raw6878step0Labels permutation40 permutation5
    mixedMoment B raw6878step1 raw6878step1Labels = mixedMoment B raw6878step2 raw6878step2Labels := by
      have ha : raw6878step2 = -raw6878step1 := by apply Matrix.ext; change ∀ i j, raw6878step2 i j = -(raw6878step1 i j); unfold raw6878step2 raw6878step1; decide +kernel
      have hl : raw6878step2Labels = raw6878step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6878step2 raw6878step2Labels = mixedMoment B raw6878step3 raw6878step3Labels := by
      have ha : raw6878step3 = raw6878step2 := by apply Matrix.ext; unfold raw6878step3 raw6878step2; decide +kernel
      have hl : raw6878step2Labels = labelEmbedding1 ∘ raw6878step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6878step2 raw6878step2Labels raw6878step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3240 node3240Labels := by rfl

def raw6879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6879Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6879step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6879step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6879step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6879step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6879step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6879 raw6879Labels = mixedMoment B node3561 node3561Labels := by
  calc
    mixedMoment B raw6879 raw6879Labels = mixedMoment B raw6879step0 raw6879step0Labels := by
      have ha : raw6879step0 = (fun i j => raw6879 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6879step0 raw6879; decide +kernel
      have hl : raw6879step0Labels = raw6879Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6879 raw6879Labels permutation157 permutation7
    mixedMoment B raw6879step0 raw6879step0Labels = mixedMoment B raw6879step1 raw6879step1Labels := by
      have ha : raw6879step1 = -raw6879step0 := by apply Matrix.ext; change ∀ i j, raw6879step1 i j = -(raw6879step0 i j); unfold raw6879step1 raw6879step0; decide +kernel
      have hl : raw6879step1Labels = raw6879step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6879step1 raw6879step1Labels = mixedMoment B raw6879step2 raw6879step2Labels := by
      have ha : raw6879step2 = raw6879step1 := by apply Matrix.ext; unfold raw6879step2 raw6879step1; decide +kernel
      have hl : raw6879step1Labels = labelEmbedding1 ∘ raw6879step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6879step1 raw6879step1Labels raw6879step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3561 node3561Labels := by rfl

def raw6880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6880Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6880step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw6880step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6880step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6880step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw6880step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6880 raw6880Labels = mixedMoment B node2835 node2835Labels := by
  calc
    mixedMoment B raw6880 raw6880Labels = mixedMoment B raw6880step0 raw6880step0Labels := by
      have hz : ∀ j, raw6880 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6880step0 = (fun i j => raw6880 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6880step0 raw6880; decide +kernel
      have hl : raw6880step0Labels = raw6880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6880 raw6880Labels permutation346 hz
    mixedMoment B raw6880step0 raw6880step0Labels = mixedMoment B raw6880step1 raw6880step1Labels := by
      have ha : raw6880step1 = (fun i j => raw6880step0 (permutation82 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6880step1 raw6880step0; decide +kernel
      have hl : raw6880step1Labels = raw6880step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6880step0 raw6880step0Labels permutation82 permutation5
    mixedMoment B raw6880step1 raw6880step1Labels = mixedMoment B raw6880step2 raw6880step2Labels := by
      have ha : raw6880step2 = -raw6880step1 := by apply Matrix.ext; change ∀ i j, raw6880step2 i j = -(raw6880step1 i j); unfold raw6880step2 raw6880step1; decide +kernel
      have hl : raw6880step2Labels = raw6880step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6880step2 raw6880step2Labels = mixedMoment B raw6880step3 raw6880step3Labels := by
      have ha : raw6880step3 = raw6880step2 := by apply Matrix.ext; unfold raw6880step3 raw6880step2; decide +kernel
      have hl : raw6880step2Labels = labelEmbedding1 ∘ raw6880step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6880step2 raw6880step2Labels raw6880step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2835 node2835Labels := by rfl

def raw6881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6881Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6881step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6881step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw6881step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6881step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6881step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6881step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6881step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6881 raw6881Labels = mixedMoment B node3577 node3577Labels := by
  calc
    mixedMoment B raw6881 raw6881Labels = mixedMoment B raw6881step0 raw6881step0Labels := by
      have hz : ∀ j, raw6881 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6881step0 = (fun i j => raw6881 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6881step0 raw6881; decide +kernel
      have hl : raw6881step0Labels = raw6881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6881 raw6881Labels permutation346 hz
    mixedMoment B raw6881step0 raw6881step0Labels = mixedMoment B raw6881step1 raw6881step1Labels := by
      have ha : raw6881step1 = (fun i j => raw6881step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6881step1 raw6881step0; decide +kernel
      have hl : raw6881step1Labels = raw6881step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6881step0 raw6881step0Labels permutation37 permutation7
    mixedMoment B raw6881step1 raw6881step1Labels = mixedMoment B raw6881step2 raw6881step2Labels := by
      have ha : raw6881step2 = -raw6881step1 := by apply Matrix.ext; change ∀ i j, raw6881step2 i j = -(raw6881step1 i j); unfold raw6881step2 raw6881step1; decide +kernel
      have hl : raw6881step2Labels = raw6881step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6881step2 raw6881step2Labels = mixedMoment B raw6881step3 raw6881step3Labels := by
      have ha : raw6881step3 = raw6881step2 := by apply Matrix.ext; unfold raw6881step3 raw6881step2; decide +kernel
      have hl : raw6881step2Labels = labelEmbedding1 ∘ raw6881step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6881step2 raw6881step2Labels raw6881step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3577 node3577Labels := by rfl

def raw6882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6882Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6882step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6882step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw6882step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6882step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6882step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6882step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6882step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6882 raw6882Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw6882 raw6882Labels = mixedMoment B raw6882step0 raw6882step0Labels := by
      have hz : ∀ j, raw6882 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6882step0 = (fun i j => raw6882 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6882step0 raw6882; decide +kernel
      have hl : raw6882step0Labels = raw6882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6882 raw6882Labels permutation346 hz
    mixedMoment B raw6882step0 raw6882step0Labels = mixedMoment B raw6882step1 raw6882step1Labels := by
      have ha : raw6882step1 = (fun i j => raw6882step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6882step1 raw6882step0; decide +kernel
      have hl : raw6882step1Labels = raw6882step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6882step0 raw6882step0Labels permutation37 permutation7
    mixedMoment B raw6882step1 raw6882step1Labels = mixedMoment B raw6882step2 raw6882step2Labels := by
      have ha : raw6882step2 = -raw6882step1 := by apply Matrix.ext; change ∀ i j, raw6882step2 i j = -(raw6882step1 i j); unfold raw6882step2 raw6882step1; decide +kernel
      have hl : raw6882step2Labels = raw6882step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6882step2 raw6882step2Labels = mixedMoment B raw6882step3 raw6882step3Labels := by
      have ha : raw6882step3 = raw6882step2 := by apply Matrix.ext; unfold raw6882step3 raw6882step2; decide +kernel
      have hl : raw6882step2Labels = labelEmbedding1 ∘ raw6882step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6882step2 raw6882step2Labels raw6882step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw6883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6883Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6883step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6883step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6883step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6883step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6883step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6883 raw6883Labels = mixedMoment B node3238 node3238Labels := by
  calc
    mixedMoment B raw6883 raw6883Labels = mixedMoment B raw6883step0 raw6883step0Labels := by
      have ha : raw6883step0 = (fun i j => raw6883 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6883step0 raw6883; decide +kernel
      have hl : raw6883step0Labels = raw6883Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6883 raw6883Labels permutation212 permutation5
    mixedMoment B raw6883step0 raw6883step0Labels = mixedMoment B raw6883step1 raw6883step1Labels := by
      have ha : raw6883step1 = -raw6883step0 := by apply Matrix.ext; change ∀ i j, raw6883step1 i j = -(raw6883step0 i j); unfold raw6883step1 raw6883step0; decide +kernel
      have hl : raw6883step1Labels = raw6883step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6883step1 raw6883step1Labels = mixedMoment B raw6883step2 raw6883step2Labels := by
      have ha : raw6883step2 = raw6883step1 := by apply Matrix.ext; unfold raw6883step2 raw6883step1; decide +kernel
      have hl : raw6883step1Labels = labelEmbedding1 ∘ raw6883step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6883step1 raw6883step1Labels raw6883step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3238 node3238Labels := by rfl

def raw6884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6884Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6884step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6884step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6884step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6884step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6884step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6884 raw6884Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw6884 raw6884Labels = mixedMoment B raw6884step0 raw6884step0Labels := by
      have ha : raw6884step0 = (fun i j => raw6884 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6884step0 raw6884; decide +kernel
      have hl : raw6884step0Labels = raw6884Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6884 raw6884Labels permutation157 permutation7
    mixedMoment B raw6884step0 raw6884step0Labels = mixedMoment B raw6884step1 raw6884step1Labels := by
      have ha : raw6884step1 = -raw6884step0 := by apply Matrix.ext; change ∀ i j, raw6884step1 i j = -(raw6884step0 i j); unfold raw6884step1 raw6884step0; decide +kernel
      have hl : raw6884step1Labels = raw6884step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6884step1 raw6884step1Labels = mixedMoment B raw6884step2 raw6884step2Labels := by
      have ha : raw6884step2 = raw6884step1 := by apply Matrix.ext; unfold raw6884step2 raw6884step1; decide +kernel
      have hl : raw6884step1Labels = labelEmbedding1 ∘ raw6884step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6884step1 raw6884step1Labels raw6884step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3464 node3464Labels := by rfl

def raw6885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6885Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw6885step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6885step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6885step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6885step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw6885step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6885 raw6885Labels = mixedMoment B node2833 node2833Labels := by
  calc
    mixedMoment B raw6885 raw6885Labels = mixedMoment B raw6885step0 raw6885step0Labels := by
      have ha : raw6885step0 = (fun i j => raw6885 (permutation443 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6885step0 raw6885; decide +kernel
      have hl : raw6885step0Labels = raw6885Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6885 raw6885Labels permutation443 permutation5
    mixedMoment B raw6885step0 raw6885step0Labels = mixedMoment B raw6885step1 raw6885step1Labels := by
      have ha : raw6885step1 = -raw6885step0 := by apply Matrix.ext; change ∀ i j, raw6885step1 i j = -(raw6885step0 i j); unfold raw6885step1 raw6885step0; decide +kernel
      have hl : raw6885step1Labels = raw6885step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6885step1 raw6885step1Labels = mixedMoment B raw6885step2 raw6885step2Labels := by
      have ha : raw6885step2 = raw6885step1 := by apply Matrix.ext; unfold raw6885step2 raw6885step1; decide +kernel
      have hl : raw6885step1Labels = labelEmbedding1 ∘ raw6885step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6885step1 raw6885step1Labels raw6885step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2833 node2833Labels := by rfl

def raw6886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6886Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw6886step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6886step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6886step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw6886step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6886 raw6886Labels = mixedMoment B node3528 node3528Labels := by
  calc
    mixedMoment B raw6886 raw6886Labels = mixedMoment B raw6886step0 raw6886step0Labels := by
      have ha : raw6886step0 = (fun i j => raw6886 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6886step0 raw6886; decide +kernel
      have hl : raw6886step0Labels = raw6886Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6886 raw6886Labels permutation157 permutation7
    mixedMoment B raw6886step0 raw6886step0Labels = mixedMoment B raw6886step1 raw6886step1Labels := by
      have ha : raw6886step1 = -raw6886step0 := by apply Matrix.ext; change ∀ i j, raw6886step1 i j = -(raw6886step0 i j); unfold raw6886step1 raw6886step0; decide +kernel
      have hl : raw6886step1Labels = raw6886step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6886step1 raw6886step1Labels = mixedMoment B raw6886step2 raw6886step2Labels := by
      have ha : raw6886step2 = raw6886step1 := by apply Matrix.ext; unfold raw6886step2 raw6886step1; decide +kernel
      have hl : raw6886step1Labels = labelEmbedding1 ∘ raw6886step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6886step1 raw6886step1Labels raw6886step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3528 node3528Labels := by rfl

def raw6887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6887Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw6887step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6887step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6887step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6887step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6887 raw6887Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw6887 raw6887Labels = mixedMoment B raw6887step0 raw6887step0Labels := by
      have ha : raw6887step0 = (fun i j => raw6887 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6887step0 raw6887; decide +kernel
      have hl : raw6887step0Labels = raw6887Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6887 raw6887Labels permutation157 permutation7
    mixedMoment B raw6887step0 raw6887step0Labels = mixedMoment B raw6887step1 raw6887step1Labels := by
      have ha : raw6887step1 = -raw6887step0 := by apply Matrix.ext; change ∀ i j, raw6887step1 i j = -(raw6887step0 i j); unfold raw6887step1 raw6887step0; decide +kernel
      have hl : raw6887step1Labels = raw6887step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6887step1 raw6887step1Labels = mixedMoment B raw6887step2 raw6887step2Labels := by
      have ha : raw6887step2 = raw6887step1 := by apply Matrix.ext; unfold raw6887step2 raw6887step1; decide +kernel
      have hl : raw6887step1Labels = labelEmbedding1 ∘ raw6887step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6887step1 raw6887step1Labels raw6887step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw6888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6888Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6888step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw6888step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6888step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6888step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6888step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6888step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6888 raw6888Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw6888 raw6888Labels = mixedMoment B raw6888step0 raw6888step0Labels := by
      have hz : ∀ j, raw6888 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6888step0 = (fun i j => raw6888 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6888step0 raw6888; decide +kernel
      have hl : raw6888step0Labels = raw6888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6888 raw6888Labels permutation346 hz
    mixedMoment B raw6888step0 raw6888step0Labels = mixedMoment B raw6888step1 raw6888step1Labels := by
      have ha : raw6888step1 = (fun i j => raw6888step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6888step1 raw6888step0; decide +kernel
      have hl : raw6888step1Labels = raw6888step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6888step0 raw6888step0Labels permutation37 permutation7
    mixedMoment B raw6888step1 raw6888step1Labels = mixedMoment B raw6888step2 raw6888step2Labels := by
      have ha : raw6888step2 = -raw6888step1 := by apply Matrix.ext; change ∀ i j, raw6888step2 i j = -(raw6888step1 i j); unfold raw6888step2 raw6888step1; decide +kernel
      have hl : raw6888step2Labels = raw6888step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6888step2 raw6888step2Labels = mixedMoment B raw6888step3 raw6888step3Labels := by
      have ha : raw6888step3 = raw6888step2 := by apply Matrix.ext; unfold raw6888step3 raw6888step2; decide +kernel
      have hl : raw6888step2Labels = labelEmbedding1 ∘ raw6888step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6888step2 raw6888step2Labels raw6888step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

def raw6889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6889Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6889step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw6889step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6889step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6889step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6889step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6889step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6889 raw6889Labels = mixedMoment B node3479 node3479Labels := by
  calc
    mixedMoment B raw6889 raw6889Labels = mixedMoment B raw6889step0 raw6889step0Labels := by
      have hz : ∀ j, raw6889 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6889step0 = (fun i j => raw6889 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6889step0 raw6889; decide +kernel
      have hl : raw6889step0Labels = raw6889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6889 raw6889Labels permutation346 hz
    mixedMoment B raw6889step0 raw6889step0Labels = mixedMoment B raw6889step1 raw6889step1Labels := by
      have ha : raw6889step1 = (fun i j => raw6889step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6889step1 raw6889step0; decide +kernel
      have hl : raw6889step1Labels = raw6889step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6889step0 raw6889step0Labels permutation37 permutation7
    mixedMoment B raw6889step1 raw6889step1Labels = mixedMoment B raw6889step2 raw6889step2Labels := by
      have ha : raw6889step2 = -raw6889step1 := by apply Matrix.ext; change ∀ i j, raw6889step2 i j = -(raw6889step1 i j); unfold raw6889step2 raw6889step1; decide +kernel
      have hl : raw6889step2Labels = raw6889step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6889step2 raw6889step2Labels = mixedMoment B raw6889step3 raw6889step3Labels := by
      have ha : raw6889step3 = raw6889step2 := by apply Matrix.ext; unfold raw6889step3 raw6889step2; decide +kernel
      have hl : raw6889step2Labels = labelEmbedding1 ∘ raw6889step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6889step2 raw6889step2Labels raw6889step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3479 node3479Labels := by rfl

def raw6890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6890Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw6890step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6890step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6890step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6890step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6890 raw6890Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw6890 raw6890Labels = mixedMoment B raw6890step0 raw6890step0Labels := by
      have ha : raw6890step0 = (fun i j => raw6890 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6890step0 raw6890; decide +kernel
      have hl : raw6890step0Labels = raw6890Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6890 raw6890Labels permutation157 permutation7
    mixedMoment B raw6890step0 raw6890step0Labels = mixedMoment B raw6890step1 raw6890step1Labels := by
      have ha : raw6890step1 = -raw6890step0 := by apply Matrix.ext; change ∀ i j, raw6890step1 i j = -(raw6890step0 i j); unfold raw6890step1 raw6890step0; decide +kernel
      have hl : raw6890step1Labels = raw6890step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6890step1 raw6890step1Labels = mixedMoment B raw6890step2 raw6890step2Labels := by
      have ha : raw6890step2 = raw6890step1 := by apply Matrix.ext; unfold raw6890step2 raw6890step1; decide +kernel
      have hl : raw6890step1Labels = labelEmbedding1 ∘ raw6890step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6890step1 raw6890step1Labels raw6890step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

def raw6891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6891Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6891step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6891step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6891step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6891step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6891step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6891step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6891 raw6891Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw6891 raw6891Labels = mixedMoment B raw6891step0 raw6891step0Labels := by
      have hz : ∀ j, raw6891 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6891step0 = (fun i j => raw6891 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6891step0 raw6891; decide +kernel
      have hl : raw6891step0Labels = raw6891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6891 raw6891Labels permutation346 hz
    mixedMoment B raw6891step0 raw6891step0Labels = mixedMoment B raw6891step1 raw6891step1Labels := by
      have ha : raw6891step1 = (fun i j => raw6891step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6891step1 raw6891step0; decide +kernel
      have hl : raw6891step1Labels = raw6891step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6891step0 raw6891step0Labels permutation37 permutation7
    mixedMoment B raw6891step1 raw6891step1Labels = mixedMoment B raw6891step2 raw6891step2Labels := by
      have ha : raw6891step2 = -raw6891step1 := by apply Matrix.ext; change ∀ i j, raw6891step2 i j = -(raw6891step1 i j); unfold raw6891step2 raw6891step1; decide +kernel
      have hl : raw6891step2Labels = raw6891step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6891step2 raw6891step2Labels = mixedMoment B raw6891step3 raw6891step3Labels := by
      have ha : raw6891step3 = raw6891step2 := by apply Matrix.ext; unfold raw6891step3 raw6891step2; decide +kernel
      have hl : raw6891step2Labels = labelEmbedding1 ∘ raw6891step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6891step2 raw6891step2Labels raw6891step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw6892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6892Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6892step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw6892step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6892step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6892step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6892step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6892step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6892 raw6892Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw6892 raw6892Labels = mixedMoment B raw6892step0 raw6892step0Labels := by
      have hz : ∀ j, raw6892 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6892step0 = (fun i j => raw6892 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6892step0 raw6892; decide +kernel
      have hl : raw6892step0Labels = raw6892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6892 raw6892Labels permutation346 hz
    mixedMoment B raw6892step0 raw6892step0Labels = mixedMoment B raw6892step1 raw6892step1Labels := by
      have ha : raw6892step1 = (fun i j => raw6892step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6892step1 raw6892step0; decide +kernel
      have hl : raw6892step1Labels = raw6892step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6892step0 raw6892step0Labels permutation37 permutation7
    mixedMoment B raw6892step1 raw6892step1Labels = mixedMoment B raw6892step2 raw6892step2Labels := by
      have ha : raw6892step2 = -raw6892step1 := by apply Matrix.ext; change ∀ i j, raw6892step2 i j = -(raw6892step1 i j); unfold raw6892step2 raw6892step1; decide +kernel
      have hl : raw6892step2Labels = raw6892step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6892step2 raw6892step2Labels = mixedMoment B raw6892step3 raw6892step3Labels := by
      have ha : raw6892step3 = raw6892step2 := by apply Matrix.ext; unfold raw6892step3 raw6892step2; decide +kernel
      have hl : raw6892step2Labels = labelEmbedding1 ∘ raw6892step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6892step2 raw6892step2Labels raw6892step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw6893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6893Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6893step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw6893step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6893step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6893step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6893step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6893 raw6893Labels = mixedMoment B node3243 node3243Labels := by
  calc
    mixedMoment B raw6893 raw6893Labels = mixedMoment B raw6893step0 raw6893step0Labels := by
      have hz : ∀ j, raw6893 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6893step0 = (fun i j => raw6893 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6893step0 raw6893; decide +kernel
      have hl : raw6893step0Labels = raw6893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6893 raw6893Labels permutation346 hz
    mixedMoment B raw6893step0 raw6893step0Labels = mixedMoment B raw6893step1 raw6893step1Labels := by
      have ha : raw6893step1 = (fun i j => raw6893step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6893step1 raw6893step0; decide +kernel
      have hl : raw6893step1Labels = raw6893step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6893step0 raw6893step0Labels permutation38 permutation5
    mixedMoment B raw6893step1 raw6893step1Labels = mixedMoment B raw6893step2 raw6893step2Labels := by
      have ha : raw6893step2 = -raw6893step1 := by apply Matrix.ext; change ∀ i j, raw6893step2 i j = -(raw6893step1 i j); unfold raw6893step2 raw6893step1; decide +kernel
      have hl : raw6893step2Labels = raw6893step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6893step2 raw6893step2Labels = mixedMoment B raw6893step3 raw6893step3Labels := by
      have ha : raw6893step3 = raw6893step2 := by apply Matrix.ext; unfold raw6893step3 raw6893step2; decide +kernel
      have hl : raw6893step2Labels = labelEmbedding1 ∘ raw6893step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6893step2 raw6893step2Labels raw6893step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3243 node3243Labels := by rfl

def raw6894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6894Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6894step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw6894step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6894step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6894step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6894step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6894 raw6894Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw6894 raw6894Labels = mixedMoment B raw6894step0 raw6894step0Labels := by
      have hz : ∀ j, raw6894 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6894step0 = (fun i j => raw6894 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6894step0 raw6894; decide +kernel
      have hl : raw6894step0Labels = raw6894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6894 raw6894Labels permutation346 hz
    mixedMoment B raw6894step0 raw6894step0Labels = mixedMoment B raw6894step1 raw6894step1Labels := by
      have ha : raw6894step1 = (fun i j => raw6894step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6894step1 raw6894step0; decide +kernel
      have hl : raw6894step1Labels = raw6894step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6894step0 raw6894step0Labels permutation37 permutation7
    mixedMoment B raw6894step1 raw6894step1Labels = mixedMoment B raw6894step2 raw6894step2Labels := by
      have ha : raw6894step2 = -raw6894step1 := by apply Matrix.ext; change ∀ i j, raw6894step2 i j = -(raw6894step1 i j); unfold raw6894step2 raw6894step1; decide +kernel
      have hl : raw6894step2Labels = raw6894step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6894step2 raw6894step2Labels = mixedMoment B raw6894step3 raw6894step3Labels := by
      have ha : raw6894step3 = raw6894step2 := by apply Matrix.ext; unfold raw6894step3 raw6894step2; decide +kernel
      have hl : raw6894step2Labels = labelEmbedding1 ∘ raw6894step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6894step2 raw6894step2Labels raw6894step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3480 node3480Labels := by rfl

def raw6895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6895Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw6895step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6895step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6895step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6895step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6895 raw6895Labels = mixedMoment B node3518 node3518Labels := by
  calc
    mixedMoment B raw6895 raw6895Labels = mixedMoment B raw6895step0 raw6895step0Labels := by
      have ha : raw6895step0 = (fun i j => raw6895 (permutation157 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6895step0 raw6895; decide +kernel
      have hl : raw6895step0Labels = raw6895Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6895 raw6895Labels permutation157 permutation7
    mixedMoment B raw6895step0 raw6895step0Labels = mixedMoment B raw6895step1 raw6895step1Labels := by
      have ha : raw6895step1 = -raw6895step0 := by apply Matrix.ext; change ∀ i j, raw6895step1 i j = -(raw6895step0 i j); unfold raw6895step1 raw6895step0; decide +kernel
      have hl : raw6895step1Labels = raw6895step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6895step1 raw6895step1Labels = mixedMoment B raw6895step2 raw6895step2Labels := by
      have ha : raw6895step2 = raw6895step1 := by apply Matrix.ext; unfold raw6895step2 raw6895step1; decide +kernel
      have hl : raw6895step1Labels = labelEmbedding1 ∘ raw6895step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6895step1 raw6895step1Labels raw6895step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3518 node3518Labels := by rfl

def raw6896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6896Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![2, -1, -1], ![2, -2, 0]]
def raw6896step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw6896step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6896step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6896step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6896step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6896 raw6896Labels = mixedMoment B node2838 node2838Labels := by
  calc
    mixedMoment B raw6896 raw6896Labels = mixedMoment B raw6896step0 raw6896step0Labels := by
      have hz : ∀ j, raw6896 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6896step0 = (fun i j => raw6896 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6896step0 raw6896; decide +kernel
      have hl : raw6896step0Labels = raw6896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6896 raw6896Labels permutation346 hz
    mixedMoment B raw6896step0 raw6896step0Labels = mixedMoment B raw6896step1 raw6896step1Labels := by
      have ha : raw6896step1 = (fun i j => raw6896step0 (permutation80 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6896step1 raw6896step0; decide +kernel
      have hl : raw6896step1Labels = raw6896step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6896step0 raw6896step0Labels permutation80 permutation5
    mixedMoment B raw6896step1 raw6896step1Labels = mixedMoment B raw6896step2 raw6896step2Labels := by
      have ha : raw6896step2 = -raw6896step1 := by apply Matrix.ext; change ∀ i j, raw6896step2 i j = -(raw6896step1 i j); unfold raw6896step2 raw6896step1; decide +kernel
      have hl : raw6896step2Labels = raw6896step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6896step2 raw6896step2Labels = mixedMoment B raw6896step3 raw6896step3Labels := by
      have ha : raw6896step3 = raw6896step2 := by apply Matrix.ext; unfold raw6896step3 raw6896step2; decide +kernel
      have hl : raw6896step2Labels = labelEmbedding1 ∘ raw6896step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6896step2 raw6896step2Labels raw6896step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2838 node2838Labels := by rfl

def raw6897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw6897Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0]]
def raw6897step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6897step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6897step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6897step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6897step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6897step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6897 raw6897Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw6897 raw6897Labels = mixedMoment B raw6897step0 raw6897step0Labels := by
      have hz : ∀ j, raw6897 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6897step0 = (fun i j => raw6897 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6897step0 raw6897; decide +kernel
      have hl : raw6897step0Labels = raw6897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6897 raw6897Labels permutation346 hz
    mixedMoment B raw6897step0 raw6897step0Labels = mixedMoment B raw6897step1 raw6897step1Labels := by
      have ha : raw6897step1 = (fun i j => raw6897step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6897step1 raw6897step0; decide +kernel
      have hl : raw6897step1Labels = raw6897step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6897step0 raw6897step0Labels permutation37 permutation7
    mixedMoment B raw6897step1 raw6897step1Labels = mixedMoment B raw6897step2 raw6897step2Labels := by
      have ha : raw6897step2 = -raw6897step1 := by apply Matrix.ext; change ∀ i j, raw6897step2 i j = -(raw6897step1 i j); unfold raw6897step2 raw6897step1; decide +kernel
      have hl : raw6897step2Labels = raw6897step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6897step2 raw6897step2Labels = mixedMoment B raw6897step3 raw6897step3Labels := by
      have ha : raw6897step3 = raw6897step2 := by apply Matrix.ext; unfold raw6897step3 raw6897step2; decide +kernel
      have hl : raw6897step2Labels = labelEmbedding1 ∘ raw6897step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6897step2 raw6897step2Labels raw6897step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw6898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6898Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6898step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw6898step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6898step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw6898step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6898 raw6898Labels = mixedMoment B node2005 node2005Labels := by
  calc
    mixedMoment B raw6898 raw6898Labels = mixedMoment B raw6898step0 raw6898step0Labels := by
      have hz : ∀ j, raw6898 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6898step0 = (fun i j => raw6898 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6898step0 raw6898; decide +kernel
      have hl : raw6898step0Labels = raw6898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6898 raw6898Labels permutation346 hz
    mixedMoment B raw6898step0 raw6898step0Labels = mixedMoment B raw6898step1 raw6898step1Labels := by
      have ha : raw6898step1 = (fun i j => raw6898step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6898step1 raw6898step0; decide +kernel
      have hl : raw6898step1Labels = raw6898step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6898step0 raw6898step0Labels permutation139 permutation5
    mixedMoment B raw6898step1 raw6898step1Labels = mixedMoment B raw6898step2 raw6898step2Labels := by
      have ha : raw6898step2 = raw6898step1 := by apply Matrix.ext; unfold raw6898step2 raw6898step1; decide +kernel
      have hl : raw6898step1Labels = labelEmbedding1 ∘ raw6898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6898step1 raw6898step1Labels raw6898step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2005 node2005Labels := by rfl

def raw6899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6899Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6899step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6899step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6899step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6899step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6899 raw6899Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw6899 raw6899Labels = mixedMoment B raw6899step0 raw6899step0Labels := by
      have hz : ∀ j, raw6899 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6899step0 = (fun i j => raw6899 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6899step0 raw6899; decide +kernel
      have hl : raw6899step0Labels = raw6899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6899 raw6899Labels permutation346 hz
    mixedMoment B raw6899step0 raw6899step0Labels = mixedMoment B raw6899step1 raw6899step1Labels := by
      have ha : raw6899step1 = (fun i j => raw6899step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6899step1 raw6899step0; decide +kernel
      have hl : raw6899step1Labels = raw6899step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6899step0 raw6899step0Labels permutation148 permutation5
    mixedMoment B raw6899step1 raw6899step1Labels = mixedMoment B raw6899step2 raw6899step2Labels := by
      have ha : raw6899step2 = raw6899step1 := by apply Matrix.ext; unfold raw6899step2 raw6899step1; decide +kernel
      have hl : raw6899step1Labels = labelEmbedding1 ∘ raw6899step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6899step1 raw6899step1Labels raw6899step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2207 node2207Labels := by rfl

def raw6900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6900Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6900step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6900step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6900 raw6900Labels = mixedMoment B node2001 node2001Labels := by
  calc
    mixedMoment B raw6900 raw6900Labels = mixedMoment B raw6900step0 raw6900step0Labels := by
      have ha : raw6900step0 = (fun i j => raw6900 (permutation619 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6900step0 raw6900; decide +kernel
      have hl : raw6900step0Labels = raw6900Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6900 raw6900Labels permutation619 permutation5
    mixedMoment B raw6900step0 raw6900step0Labels = mixedMoment B raw6900step1 raw6900step1Labels := by
      have ha : raw6900step1 = raw6900step0 := by apply Matrix.ext; unfold raw6900step1 raw6900step0; decide +kernel
      have hl : raw6900step0Labels = labelEmbedding1 ∘ raw6900step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6900step0 raw6900step0Labels raw6900step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2001 node2001Labels := by rfl

def raw6901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6901Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw6901step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6901step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw6901step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6901step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw6901step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6901 raw6901Labels = mixedMoment B node2004 node2004Labels := by
  calc
    mixedMoment B raw6901 raw6901Labels = mixedMoment B raw6901step0 raw6901step0Labels := by
      have hz : ∀ j, raw6901 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6901step0 = (fun i j => raw6901 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6901step0 raw6901; decide +kernel
      have hl : raw6901step0Labels = raw6901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6901 raw6901Labels permutation346 hz
    mixedMoment B raw6901step0 raw6901step0Labels = mixedMoment B raw6901step1 raw6901step1Labels := by
      have ha : raw6901step1 = (fun i j => raw6901step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6901step1 raw6901step0; decide +kernel
      have hl : raw6901step1Labels = raw6901step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6901step0 raw6901step0Labels permutation138 permutation5
    mixedMoment B raw6901step1 raw6901step1Labels = mixedMoment B raw6901step2 raw6901step2Labels := by
      have ha : raw6901step2 = raw6901step1 := by apply Matrix.ext; unfold raw6901step2 raw6901step1; decide +kernel
      have hl : raw6901step1Labels = labelEmbedding1 ∘ raw6901step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6901step1 raw6901step1Labels raw6901step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2004 node2004Labels := by rfl

def raw6902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw6902Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw6902step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw6902step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6902step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw6902step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6902 raw6902Labels = mixedMoment B node2055 node2055Labels := by
  calc
    mixedMoment B raw6902 raw6902Labels = mixedMoment B raw6902step0 raw6902step0Labels := by
      have hz : ∀ j, raw6902 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6902step0 = (fun i j => raw6902 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6902step0 raw6902; decide +kernel
      have hl : raw6902step0Labels = raw6902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6902 raw6902Labels permutation346 hz
    mixedMoment B raw6902step0 raw6902step0Labels = mixedMoment B raw6902step1 raw6902step1Labels := by
      have ha : raw6902step1 = (fun i j => raw6902step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6902step1 raw6902step0; decide +kernel
      have hl : raw6902step1Labels = raw6902step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6902step0 raw6902step0Labels permutation138 permutation5
    mixedMoment B raw6902step1 raw6902step1Labels = mixedMoment B raw6902step2 raw6902step2Labels := by
      have ha : raw6902step2 = raw6902step1 := by apply Matrix.ext; unfold raw6902step2 raw6902step1; decide +kernel
      have hl : raw6902step1Labels = labelEmbedding1 ∘ raw6902step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6902step1 raw6902step1Labels raw6902step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2055 node2055Labels := by rfl

def raw6903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6903 raw6903Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw6903 raw6903Labels = mixedMoment B raw6903step0 raw6903step0Labels := by
      have hz : ∀ j, raw6903 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6903step0 = (fun i j => raw6903 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6903step0 raw6903; decide +kernel
      have hl : raw6903step0Labels = raw6903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6903 raw6903Labels permutation346 hz
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw6904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6904 raw6904Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw6904 raw6904Labels = mixedMoment B raw6904step0 raw6904step0Labels := by
      have hz : ∀ j, raw6904 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6904step0 = (fun i j => raw6904 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6904step0 raw6904; decide +kernel
      have hl : raw6904step0Labels = raw6904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6904 raw6904Labels permutation346 hz
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw6905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6905 raw6905Labels = mixedMoment B node3841 node3841Labels := by
  calc
    mixedMoment B raw6905 raw6905Labels = mixedMoment B raw6905step0 raw6905step0Labels := by
      have ha : raw6905step0 = (fun i j => raw6905 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6905step0 raw6905; decide +kernel
      have hl : raw6905step0Labels = raw6905Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6905 raw6905Labels permutation176 permutation2
    _ = mixedMoment B node3841 node3841Labels := by rfl

def raw6906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6906step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6906step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6906 raw6906Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw6906 raw6906Labels = mixedMoment B raw6906step0 raw6906step0Labels := by
      have hz : ∀ j, raw6906 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6906step0 = (fun i j => raw6906 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6906step0 raw6906; decide +kernel
      have hl : raw6906step0Labels = raw6906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6906 raw6906Labels permutation346 hz
    mixedMoment B raw6906step0 raw6906step0Labels = mixedMoment B raw6906step1 raw6906step1Labels := by
      have ha : raw6906step1 = (fun i j => raw6906step0 (permutation92 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6906step1 raw6906step0; decide +kernel
      have hl : raw6906step1Labels = raw6906step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6906step0 raw6906step0Labels permutation92 permutation4
    mixedMoment B raw6906step1 raw6906step1Labels = mixedMoment B raw6906step2 raw6906step2Labels := by
      have ha : raw6906step2 = -raw6906step1 := by apply Matrix.ext; change ∀ i j, raw6906step2 i j = -(raw6906step1 i j); unfold raw6906step2 raw6906step1; decide +kernel
      have hl : raw6906step2Labels = raw6906step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw6907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0]]
def raw6907step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6907step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6907step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6907 raw6907Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw6907 raw6907Labels = mixedMoment B raw6907step0 raw6907step0Labels := by
      have hz : ∀ j, raw6907 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6907step0 = (fun i j => raw6907 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6907step0 raw6907; decide +kernel
      have hl : raw6907step0Labels = raw6907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6907 raw6907Labels permutation346 hz
    mixedMoment B raw6907step0 raw6907step0Labels = mixedMoment B raw6907step1 raw6907step1Labels := by
      have ha : raw6907step1 = (fun i j => raw6907step0 (permutation92 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6907step1 raw6907step0; decide +kernel
      have hl : raw6907step1Labels = raw6907step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6907step0 raw6907step0Labels permutation92 permutation4
    mixedMoment B raw6907step1 raw6907step1Labels = mixedMoment B raw6907step2 raw6907step2Labels := by
      have ha : raw6907step2 = -raw6907step1 := by apply Matrix.ext; change ∀ i j, raw6907step2 i j = -(raw6907step1 i j); unfold raw6907step2 raw6907step1; decide +kernel
      have hl : raw6907step2Labels = raw6907step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw6908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0]]
def raw6908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6908step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6908 raw6908Labels = mixedMoment B node3906 node3906Labels := by
  calc
    mixedMoment B raw6908 raw6908Labels = mixedMoment B raw6908step0 raw6908step0Labels := by
      have hz : ∀ j, raw6908 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6908step0 = (fun i j => raw6908 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6908step0 raw6908; decide +kernel
      have hl : raw6908step0Labels = raw6908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6908 raw6908Labels permutation346 hz
    mixedMoment B raw6908step0 raw6908step0Labels = mixedMoment B raw6908step1 raw6908step1Labels := by
      have ha : raw6908step1 = (fun i j => raw6908step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6908step1 raw6908step0; decide +kernel
      have hl : raw6908step1Labels = raw6908step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6908step0 raw6908step0Labels permutation33 permutation2
    _ = mixedMoment B node3906 node3906Labels := by rfl

def raw6909 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![1, -1], ![0, 0]]
def raw6909Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6909step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![1, -1]]
def raw6909step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6909step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw6909step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6909step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw6909step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical6909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6909 raw6909Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw6909 raw6909Labels = mixedMoment B raw6909step0 raw6909step0Labels := by
      have hz : ∀ j, raw6909 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw6909step0 = (fun i j => raw6909 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw6909step0 raw6909; decide +kernel
      have hl : raw6909step0Labels = raw6909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6909 raw6909Labels permutation590 hz
    mixedMoment B raw6909step0 raw6909step0Labels = mixedMoment B raw6909step1 raw6909step1Labels := by
      have hz : ∀ j, raw6909step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6909step1 = (fun i j => raw6909step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6909step1 raw6909step0; decide +kernel
      have hl : raw6909step1Labels = raw6909step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6909step0 raw6909step0Labels permutation80 hz
    mixedMoment B raw6909step1 raw6909step1Labels = mixedMoment B raw6909step2 raw6909step2Labels := by
      have ha : raw6909step2 = (fun i j => raw6909step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw6909step2 raw6909step1; decide +kernel
      have hl : raw6909step2Labels = raw6909step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6909step1 raw6909step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw6910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw6910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6910 raw6910Labels = mixedMoment B node1278 node1278Labels := by
  calc
    mixedMoment B raw6910 raw6910Labels = mixedMoment B raw6910step0 raw6910step0Labels := by
      have hz : ∀ j, raw6910 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6910step0 = (fun i j => raw6910 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6910step0 raw6910; decide +kernel
      have hl : raw6910step0Labels = raw6910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6910 raw6910Labels permutation346 hz
    mixedMoment B raw6910step0 raw6910step0Labels = mixedMoment B raw6910step1 raw6910step1Labels := by
      have ha : raw6910step1 = (fun i j => raw6910step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6910step1 raw6910step0; decide +kernel
      have hl : raw6910step1Labels = raw6910step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6910step0 raw6910step0Labels permutation38 permutation2
    _ = mixedMoment B node1278 node1278Labels := by rfl

def raw6911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw6911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6911 raw6911Labels = mixedMoment B node1223 node1223Labels := by
  calc
    mixedMoment B raw6911 raw6911Labels = mixedMoment B raw6911step0 raw6911step0Labels := by
      have ha : raw6911step0 = (fun i j => raw6911 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6911step0 raw6911; decide +kernel
      have hl : raw6911step0Labels = raw6911Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6911 raw6911Labels permutation158 permutation2
    _ = mixedMoment B node1223 node1223Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
