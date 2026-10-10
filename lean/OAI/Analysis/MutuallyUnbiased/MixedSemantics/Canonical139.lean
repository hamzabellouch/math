import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17792Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17792step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17792 raw17792Labels = mixedMoment B node3942 node3942Labels := by
  calc
    mixedMoment B raw17792 raw17792Labels = mixedMoment B raw17792step0 raw17792step0Labels := by
      have ha : raw17792step0 = (fun i j => raw17792 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17792step0 raw17792; decide +kernel
      have hl : raw17792step0Labels = raw17792Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17792 raw17792Labels permutation200 permutation3
    _ = mixedMoment B node3942 node3942Labels := by rfl

def raw17793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17793Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17793step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17793step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17793 raw17793Labels = mixedMoment B node3971 node3971Labels := by
  calc
    mixedMoment B raw17793 raw17793Labels = mixedMoment B raw17793step0 raw17793step0Labels := by
      have ha : raw17793step0 = (fun i j => raw17793 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17793step0 raw17793; decide +kernel
      have hl : raw17793step0Labels = raw17793Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17793 raw17793Labels permutation160 permutation3
    _ = mixedMoment B node3971 node3971Labels := by rfl

def raw17794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17794Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17794step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17794step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17794 raw17794Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw17794 raw17794Labels = mixedMoment B raw17794step0 raw17794step0Labels := by
      have ha : raw17794step0 = (fun i j => raw17794 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17794step0 raw17794; decide +kernel
      have hl : raw17794step0Labels = raw17794Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17794 raw17794Labels permutation162 permutation3
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw17795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17795Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17795step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17795step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17795 raw17795Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw17795 raw17795Labels = mixedMoment B raw17795step0 raw17795step0Labels := by
      have hz : ∀ j, raw17795 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17795step0 = (fun i j => raw17795 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17795step0 raw17795; decide +kernel
      have hl : raw17795step0Labels = raw17795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17795 raw17795Labels permutation346 hz
    mixedMoment B raw17795step0 raw17795step0Labels = mixedMoment B raw17795step1 raw17795step1Labels := by
      have ha : raw17795step1 = (fun i j => raw17795step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17795step1 raw17795step0; decide +kernel
      have hl : raw17795step1Labels = raw17795step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17795step0 raw17795step0Labels permutation56 permutation3
    _ = mixedMoment B node3705 node3705Labels := by rfl

def raw17796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17796Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17796step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17796 raw17796Labels = mixedMoment B node3945 node3945Labels := by
  calc
    mixedMoment B raw17796 raw17796Labels = mixedMoment B raw17796step0 raw17796step0Labels := by
      have ha : raw17796step0 = (fun i j => raw17796 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17796step0 raw17796; decide +kernel
      have hl : raw17796step0Labels = raw17796Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17796 raw17796Labels permutation686 permutation3
    mixedMoment B raw17796step0 raw17796step0Labels = mixedMoment B raw17796step1 raw17796step1Labels := by
      have ha : raw17796step1 = -raw17796step0 := by apply Matrix.ext; change ∀ i j, raw17796step1 i j = -(raw17796step0 i j); unfold raw17796step1 raw17796step0; decide +kernel
      have hl : raw17796step1Labels = raw17796step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3945 node3945Labels := by rfl

def raw17797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17797Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw17797step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17797step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17797step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17797 raw17797Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw17797 raw17797Labels = mixedMoment B raw17797step0 raw17797step0Labels := by
      have hz : ∀ j, raw17797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17797step0 = (fun i j => raw17797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17797step0 raw17797; decide +kernel
      have hl : raw17797step0Labels = raw17797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17797 raw17797Labels permutation346 hz
    mixedMoment B raw17797step0 raw17797step0Labels = mixedMoment B raw17797step1 raw17797step1Labels := by
      have ha : raw17797step1 = (fun i j => raw17797step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17797step1 raw17797step0; decide +kernel
      have hl : raw17797step1Labels = raw17797step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17797step0 raw17797step0Labels permutation34 permutation3
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw17798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17798Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17798step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17798step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17798 raw17798Labels = mixedMoment B node3984 node3984Labels := by
  calc
    mixedMoment B raw17798 raw17798Labels = mixedMoment B raw17798step0 raw17798step0Labels := by
      have hz : ∀ j, raw17798 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17798step0 = (fun i j => raw17798 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17798step0 raw17798; decide +kernel
      have hl : raw17798step0Labels = raw17798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17798 raw17798Labels permutation346 hz
    mixedMoment B raw17798step0 raw17798step0Labels = mixedMoment B raw17798step1 raw17798step1Labels := by
      have ha : raw17798step1 = (fun i j => raw17798step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17798step1 raw17798step0; decide +kernel
      have hl : raw17798step1Labels = raw17798step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17798step0 raw17798step0Labels permutation33 permutation3
    _ = mixedMoment B node3984 node3984Labels := by rfl

def raw17799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17799Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17799step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17799step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17799step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17799 raw17799Labels = mixedMoment B node3344 node3344Labels := by
  calc
    mixedMoment B raw17799 raw17799Labels = mixedMoment B raw17799step0 raw17799step0Labels := by
      have hz : ∀ j, raw17799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17799step0 = (fun i j => raw17799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17799step0 raw17799; decide +kernel
      have hl : raw17799step0Labels = raw17799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17799 raw17799Labels permutation346 hz
    mixedMoment B raw17799step0 raw17799step0Labels = mixedMoment B raw17799step1 raw17799step1Labels := by
      have ha : raw17799step1 = (fun i j => raw17799step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17799step1 raw17799step0; decide +kernel
      have hl : raw17799step1Labels = raw17799step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17799step0 raw17799step0Labels permutation126 permutation3
    mixedMoment B raw17799step1 raw17799step1Labels = mixedMoment B raw17799step2 raw17799step2Labels := by
      have ha : raw17799step2 = -raw17799step1 := by apply Matrix.ext; change ∀ i j, raw17799step2 i j = -(raw17799step1 i j); unfold raw17799step2 raw17799step1; decide +kernel
      have hl : raw17799step2Labels = raw17799step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3344 node3344Labels := by rfl

def raw17800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17800Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17800step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17800step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17800step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17800step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17800 raw17800Labels = mixedMoment B node3341 node3341Labels := by
  calc
    mixedMoment B raw17800 raw17800Labels = mixedMoment B raw17800step0 raw17800step0Labels := by
      have ha : raw17800step0 = (fun i j => raw17800 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17800step0 raw17800; decide +kernel
      have hl : raw17800step0Labels = raw17800Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17800 raw17800Labels permutation587 permutation3
    mixedMoment B raw17800step0 raw17800step0Labels = mixedMoment B raw17800step1 raw17800step1Labels := by
      have ha : raw17800step1 = -raw17800step0 := by apply Matrix.ext; change ∀ i j, raw17800step1 i j = -(raw17800step0 i j); unfold raw17800step1 raw17800step0; decide +kernel
      have hl : raw17800step1Labels = raw17800step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3341 node3341Labels := by rfl

def raw17801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17801Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17801step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw17801step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17801step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17801step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17801step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17801 raw17801Labels = mixedMoment B node3357 node3357Labels := by
  calc
    mixedMoment B raw17801 raw17801Labels = mixedMoment B raw17801step0 raw17801step0Labels := by
      have hz : ∀ j, raw17801 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17801step0 = (fun i j => raw17801 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17801step0 raw17801; decide +kernel
      have hl : raw17801step0Labels = raw17801Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17801 raw17801Labels permutation346 hz
    mixedMoment B raw17801step0 raw17801step0Labels = mixedMoment B raw17801step1 raw17801step1Labels := by
      have ha : raw17801step1 = (fun i j => raw17801step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17801step1 raw17801step0; decide +kernel
      have hl : raw17801step1Labels = raw17801step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17801step0 raw17801step0Labels permutation125 permutation3
    mixedMoment B raw17801step1 raw17801step1Labels = mixedMoment B raw17801step2 raw17801step2Labels := by
      have ha : raw17801step2 = -raw17801step1 := by apply Matrix.ext; change ∀ i j, raw17801step2 i j = -(raw17801step1 i j); unfold raw17801step2 raw17801step1; decide +kernel
      have hl : raw17801step2Labels = raw17801step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3357 node3357Labels := by rfl

def raw17802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw17802Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw17802step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17802step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17802step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17802 raw17802Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw17802 raw17802Labels = mixedMoment B raw17802step0 raw17802step0Labels := by
      have hz : ∀ j, raw17802 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17802step0 = (fun i j => raw17802 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17802step0 raw17802; decide +kernel
      have hl : raw17802step0Labels = raw17802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17802 raw17802Labels permutation346 hz
    mixedMoment B raw17802step0 raw17802step0Labels = mixedMoment B raw17802step1 raw17802step1Labels := by
      have ha : raw17802step1 = (fun i j => raw17802step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17802step1 raw17802step0; decide +kernel
      have hl : raw17802step1Labels = raw17802step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17802step0 raw17802step0Labels permutation127 permutation3
    mixedMoment B raw17802step1 raw17802step1Labels = mixedMoment B raw17802step2 raw17802step2Labels := by
      have ha : raw17802step2 = -raw17802step1 := by apply Matrix.ext; change ∀ i j, raw17802step2 i j = -(raw17802step1 i j); unfold raw17802step2 raw17802step1; decide +kernel
      have hl : raw17802step2Labels = raw17802step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw17803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17803Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17803step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17803step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17803step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17803step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17803 raw17803Labels = mixedMoment B node2388 node2388Labels := by
  calc
    mixedMoment B raw17803 raw17803Labels = mixedMoment B raw17803step0 raw17803step0Labels := by
      have hz : ∀ j, raw17803 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17803step0 = (fun i j => raw17803 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17803step0 raw17803; decide +kernel
      have hl : raw17803step0Labels = raw17803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17803 raw17803Labels permutation346 hz
    mixedMoment B raw17803step0 raw17803step0Labels = mixedMoment B raw17803step1 raw17803step1Labels := by
      have ha : raw17803step1 = (fun i j => raw17803step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17803step1 raw17803step0; decide +kernel
      have hl : raw17803step1Labels = raw17803step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17803step0 raw17803step0Labels permutation150 permutation3
    mixedMoment B raw17803step1 raw17803step1Labels = mixedMoment B raw17803step2 raw17803step2Labels := by
      have ha : raw17803step2 = -raw17803step1 := by apply Matrix.ext; change ∀ i j, raw17803step2 i j = -(raw17803step1 i j); unfold raw17803step2 raw17803step1; decide +kernel
      have hl : raw17803step2Labels = raw17803step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2388 node2388Labels := by rfl

def raw17804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17804Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17804step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17804step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17804step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17804 raw17804Labels = mixedMoment B node2383 node2383Labels := by
  calc
    mixedMoment B raw17804 raw17804Labels = mixedMoment B raw17804step0 raw17804step0Labels := by
      have ha : raw17804step0 = (fun i j => raw17804 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17804step0 raw17804; decide +kernel
      have hl : raw17804step0Labels = raw17804Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17804 raw17804Labels permutation686 permutation3
    mixedMoment B raw17804step0 raw17804step0Labels = mixedMoment B raw17804step1 raw17804step1Labels := by
      have ha : raw17804step1 = -raw17804step0 := by apply Matrix.ext; change ∀ i j, raw17804step1 i j = -(raw17804step0 i j); unfold raw17804step1 raw17804step0; decide +kernel
      have hl : raw17804step1Labels = raw17804step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2383 node2383Labels := by rfl

def raw17805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17805Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17805step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw17805step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17805step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17805step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17805step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17805step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17805 raw17805Labels = mixedMoment B node2404 node2404Labels := by
  calc
    mixedMoment B raw17805 raw17805Labels = mixedMoment B raw17805step0 raw17805step0Labels := by
      have hz : ∀ j, raw17805 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17805step0 = (fun i j => raw17805 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17805step0 raw17805; decide +kernel
      have hl : raw17805step0Labels = raw17805Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17805 raw17805Labels permutation346 hz
    mixedMoment B raw17805step0 raw17805step0Labels = mixedMoment B raw17805step1 raw17805step1Labels := by
      have ha : raw17805step1 = (fun i j => raw17805step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17805step1 raw17805step0; decide +kernel
      have hl : raw17805step1Labels = raw17805step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17805step0 raw17805step0Labels permutation149 permutation3
    mixedMoment B raw17805step1 raw17805step1Labels = mixedMoment B raw17805step2 raw17805step2Labels := by
      have ha : raw17805step2 = -raw17805step1 := by apply Matrix.ext; change ∀ i j, raw17805step2 i j = -(raw17805step1 i j); unfold raw17805step2 raw17805step1; decide +kernel
      have hl : raw17805step2Labels = raw17805step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2404 node2404Labels := by rfl

def raw17806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw17806Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw17806step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17806step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17806step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17806step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17806 raw17806Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw17806 raw17806Labels = mixedMoment B raw17806step0 raw17806step0Labels := by
      have hz : ∀ j, raw17806 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17806step0 = (fun i j => raw17806 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17806step0 raw17806; decide +kernel
      have hl : raw17806step0Labels = raw17806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17806 raw17806Labels permutation346 hz
    mixedMoment B raw17806step0 raw17806step0Labels = mixedMoment B raw17806step1 raw17806step1Labels := by
      have ha : raw17806step1 = (fun i j => raw17806step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17806step1 raw17806step0; decide +kernel
      have hl : raw17806step1Labels = raw17806step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17806step0 raw17806step0Labels permutation151 permutation3
    mixedMoment B raw17806step1 raw17806step1Labels = mixedMoment B raw17806step2 raw17806step2Labels := by
      have ha : raw17806step2 = -raw17806step1 := by apply Matrix.ext; change ∀ i j, raw17806step2 i j = -(raw17806step1 i j); unfold raw17806step2 raw17806step1; decide +kernel
      have hl : raw17806step2Labels = raw17806step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw17807 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17807Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17807step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17807step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17807step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17807step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17807 raw17807Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw17807 raw17807Labels = mixedMoment B raw17807step0 raw17807step0Labels := by
      have hz : ∀ j, raw17807 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17807step0 = (fun i j => raw17807 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17807step0 raw17807; decide +kernel
      have hl : raw17807step0Labels = raw17807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17807 raw17807Labels permutation346 hz
    mixedMoment B raw17807step0 raw17807step0Labels = mixedMoment B raw17807step1 raw17807step1Labels := by
      have ha : raw17807step1 = (fun i j => raw17807step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17807step1 raw17807step0; decide +kernel
      have hl : raw17807step1Labels = raw17807step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17807step0 raw17807step0Labels permutation32 permutation7
    mixedMoment B raw17807step1 raw17807step1Labels = mixedMoment B raw17807step2 raw17807step2Labels := by
      have ha : raw17807step2 = raw17807step1 := by apply Matrix.ext; unfold raw17807step2 raw17807step1; decide +kernel
      have hl : raw17807step1Labels = labelEmbedding10 ∘ raw17807step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17807step1 raw17807step1Labels raw17807step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw17808 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17808Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17808step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17808step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17808step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17808 raw17808Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw17808 raw17808Labels = mixedMoment B raw17808step0 raw17808step0Labels := by
      have ha : raw17808step0 = (fun i j => raw17808 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17808step0 raw17808; decide +kernel
      have hl : raw17808step0Labels = raw17808Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17808 raw17808Labels permutation152 permutation7
    mixedMoment B raw17808step0 raw17808step0Labels = mixedMoment B raw17808step1 raw17808step1Labels := by
      have ha : raw17808step1 = raw17808step0 := by apply Matrix.ext; unfold raw17808step1 raw17808step0; decide +kernel
      have hl : raw17808step0Labels = labelEmbedding10 ∘ raw17808step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17808step0 raw17808step0Labels raw17808step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw17809 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17809Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17809step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17809step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17809step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw17809step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17809step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw17809step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17809step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw17809step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17809 raw17809Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw17809 raw17809Labels = mixedMoment B raw17809step0 raw17809step0Labels := by
      have hz : ∀ j, raw17809 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17809step0 = (fun i j => raw17809 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17809step0 raw17809; decide +kernel
      have hl : raw17809step0Labels = raw17809Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17809 raw17809Labels permutation346 hz
    mixedMoment B raw17809step0 raw17809step0Labels = mixedMoment B raw17809step1 raw17809step1Labels := by
      have ha : raw17809step1 = (fun i j => raw17809step0 (permutation87 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17809step1 raw17809step0; decide +kernel
      have hl : raw17809step1Labels = raw17809step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17809step0 raw17809step0Labels permutation87 permutation5
    mixedMoment B raw17809step1 raw17809step1Labels = mixedMoment B raw17809step2 raw17809step2Labels := by
      have ha : raw17809step2 = -raw17809step1 := by apply Matrix.ext; change ∀ i j, raw17809step2 i j = -(raw17809step1 i j); unfold raw17809step2 raw17809step1; decide +kernel
      have hl : raw17809step2Labels = raw17809step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17809step2 raw17809step2Labels = mixedMoment B raw17809step3 raw17809step3Labels := by
      have ha : raw17809step3 = raw17809step2 := by apply Matrix.ext; unfold raw17809step3 raw17809step2; decide +kernel
      have hl : raw17809step2Labels = labelEmbedding8 ∘ raw17809step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17809step2 raw17809step2Labels raw17809step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

def raw17810 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17810Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17810step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17810step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17810 raw17810Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw17810 raw17810Labels = mixedMoment B raw17810step0 raw17810step0Labels := by
      have hz : ∀ j, raw17810 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17810step0 = (fun i j => raw17810 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17810step0 raw17810; decide +kernel
      have hl : raw17810step0Labels = raw17810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17810 raw17810Labels permutation346 hz
    mixedMoment B raw17810step0 raw17810step0Labels = mixedMoment B raw17810step1 raw17810step1Labels := by
      have ha : raw17810step1 = (fun i j => raw17810step0 (permutation143 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17810step1 raw17810step0; decide +kernel
      have hl : raw17810step1Labels = raw17810step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17810step0 raw17810step0Labels permutation143 permutation2
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw17811 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17811Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17811step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17811step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17811step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17811step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17811step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17811 raw17811Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw17811 raw17811Labels = mixedMoment B raw17811step0 raw17811step0Labels := by
      have ha : raw17811step0 = (fun i j => raw17811 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17811step0 raw17811; decide +kernel
      have hl : raw17811step0Labels = raw17811Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17811 raw17811Labels permutation682 permutation6
    mixedMoment B raw17811step0 raw17811step0Labels = mixedMoment B raw17811step1 raw17811step1Labels := by
      have ha : raw17811step1 = -raw17811step0 := by apply Matrix.ext; change ∀ i j, raw17811step1 i j = -(raw17811step0 i j); unfold raw17811step1 raw17811step0; decide +kernel
      have hl : raw17811step1Labels = raw17811step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17811step1 raw17811step1Labels = mixedMoment B raw17811step2 raw17811step2Labels := by
      have ha : raw17811step2 = raw17811step1 := by apply Matrix.ext; unfold raw17811step2 raw17811step1; decide +kernel
      have hl : raw17811step1Labels = labelEmbedding9 ∘ raw17811step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17811step1 raw17811step1Labels raw17811step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5471 node5471Labels := by rfl

def raw17812 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17812Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17812step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17812step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17812step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17812step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17812step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17812step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17812 raw17812Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw17812 raw17812Labels = mixedMoment B raw17812step0 raw17812step0Labels := by
      have hz : ∀ j, raw17812 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17812step0 = (fun i j => raw17812 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17812step0 raw17812; decide +kernel
      have hl : raw17812step0Labels = raw17812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17812 raw17812Labels permutation346 hz
    mixedMoment B raw17812step0 raw17812step0Labels = mixedMoment B raw17812step1 raw17812step1Labels := by
      have ha : raw17812step1 = (fun i j => raw17812step0 (permutation81 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17812step1 raw17812step0; decide +kernel
      have hl : raw17812step1Labels = raw17812step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17812step0 raw17812step0Labels permutation81 permutation5
    mixedMoment B raw17812step1 raw17812step1Labels = mixedMoment B raw17812step2 raw17812step2Labels := by
      have ha : raw17812step2 = -raw17812step1 := by apply Matrix.ext; change ∀ i j, raw17812step2 i j = -(raw17812step1 i j); unfold raw17812step2 raw17812step1; decide +kernel
      have hl : raw17812step2Labels = raw17812step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17812step2 raw17812step2Labels = mixedMoment B raw17812step3 raw17812step3Labels := by
      have ha : raw17812step3 = raw17812step2 := by apply Matrix.ext; unfold raw17812step3 raw17812step2; decide +kernel
      have hl : raw17812step2Labels = labelEmbedding8 ∘ raw17812step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17812step2 raw17812step2Labels raw17812step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw17813 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17813Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17813step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17813step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -2, 1], ![-1, -1, 2]]
def raw17813step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17813step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17813step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17813step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17813step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17813 raw17813Labels = mixedMoment B node5475 node5475Labels := by
  calc
    mixedMoment B raw17813 raw17813Labels = mixedMoment B raw17813step0 raw17813step0Labels := by
      have hz : ∀ j, raw17813 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17813step0 = (fun i j => raw17813 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17813step0 raw17813; decide +kernel
      have hl : raw17813step0Labels = raw17813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17813 raw17813Labels permutation434 hz
    mixedMoment B raw17813step0 raw17813step0Labels = mixedMoment B raw17813step1 raw17813step1Labels := by
      have hz : ∀ j, raw17813step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17813step1 = (fun i j => raw17813step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17813step1 raw17813step0; decide +kernel
      have hl : raw17813step1Labels = raw17813step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17813step0 raw17813step0Labels permutation80 hz
    mixedMoment B raw17813step1 raw17813step1Labels = mixedMoment B raw17813step2 raw17813step2Labels := by
      have ha : raw17813step2 = (fun i j => raw17813step1 (permutation24 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17813step2 raw17813step1; decide +kernel
      have hl : raw17813step2Labels = raw17813step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17813step1 raw17813step1Labels permutation24 permutation4
    mixedMoment B raw17813step2 raw17813step2Labels = mixedMoment B raw17813step3 raw17813step3Labels := by
      have ha : raw17813step3 = raw17813step2 := by apply Matrix.ext; unfold raw17813step3 raw17813step2; decide +kernel
      have hl : raw17813step2Labels = labelEmbedding7 ∘ raw17813step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17813step2 raw17813step2Labels raw17813step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5475 node5475Labels := by rfl

def raw17814 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17814Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17814step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17814step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17814step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17814step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17814step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17814step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17814 raw17814Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw17814 raw17814Labels = mixedMoment B raw17814step0 raw17814step0Labels := by
      have hz : ∀ j, raw17814 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17814step0 = (fun i j => raw17814 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17814step0 raw17814; decide +kernel
      have hl : raw17814step0Labels = raw17814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17814 raw17814Labels permutation434 hz
    mixedMoment B raw17814step0 raw17814step0Labels = mixedMoment B raw17814step1 raw17814step1Labels := by
      have ha : raw17814step1 = (fun i j => raw17814step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17814step1 raw17814step0; decide +kernel
      have hl : raw17814step1Labels = raw17814step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17814step0 raw17814step0Labels permutation151 permutation6
    mixedMoment B raw17814step1 raw17814step1Labels = mixedMoment B raw17814step2 raw17814step2Labels := by
      have ha : raw17814step2 = -raw17814step1 := by apply Matrix.ext; change ∀ i j, raw17814step2 i j = -(raw17814step1 i j); unfold raw17814step2 raw17814step1; decide +kernel
      have hl : raw17814step2Labels = raw17814step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17814step2 raw17814step2Labels = mixedMoment B raw17814step3 raw17814step3Labels := by
      have ha : raw17814step3 = raw17814step2 := by apply Matrix.ext; unfold raw17814step3 raw17814step2; decide +kernel
      have hl : raw17814step2Labels = labelEmbedding9 ∘ raw17814step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17814step2 raw17814step2Labels raw17814step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw17815 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17815Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17815step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17815step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17815step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17815 raw17815Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw17815 raw17815Labels = mixedMoment B raw17815step0 raw17815step0Labels := by
      have hz : ∀ j, raw17815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17815step0 = (fun i j => raw17815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17815step0 raw17815; decide +kernel
      have hl : raw17815step0Labels = raw17815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17815 raw17815Labels permutation346 hz
    mixedMoment B raw17815step0 raw17815step0Labels = mixedMoment B raw17815step1 raw17815step1Labels := by
      have ha : raw17815step1 = (fun i j => raw17815step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17815step1 raw17815step0; decide +kernel
      have hl : raw17815step1Labels = raw17815step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17815step0 raw17815step0Labels permutation125 permutation5
    mixedMoment B raw17815step1 raw17815step1Labels = mixedMoment B raw17815step2 raw17815step2Labels := by
      have ha : raw17815step2 = raw17815step1 := by apply Matrix.ext; unfold raw17815step2 raw17815step1; decide +kernel
      have hl : raw17815step1Labels = labelEmbedding8 ∘ raw17815step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17815step1 raw17815step1Labels raw17815step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw17816 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17816Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17816step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17816step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17816step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17816 raw17816Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw17816 raw17816Labels = mixedMoment B raw17816step0 raw17816step0Labels := by
      have hz : ∀ j, raw17816 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17816step0 = (fun i j => raw17816 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17816step0 raw17816; decide +kernel
      have hl : raw17816step0Labels = raw17816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17816 raw17816Labels permutation346 hz
    mixedMoment B raw17816step0 raw17816step0Labels = mixedMoment B raw17816step1 raw17816step1Labels := by
      have ha : raw17816step1 = (fun i j => raw17816step0 (permutation123 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17816step1 raw17816step0; decide +kernel
      have hl : raw17816step1Labels = raw17816step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17816step0 raw17816step0Labels permutation123 permutation5
    mixedMoment B raw17816step1 raw17816step1Labels = mixedMoment B raw17816step2 raw17816step2Labels := by
      have ha : raw17816step2 = raw17816step1 := by apply Matrix.ext; unfold raw17816step2 raw17816step1; decide +kernel
      have hl : raw17816step1Labels = labelEmbedding8 ∘ raw17816step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17816step1 raw17816step1Labels raw17816step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5199 node5199Labels := by rfl

def raw17817 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17817step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17817step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17817step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17817 raw17817Labels = mixedMoment B node5197 node5197Labels := by
  calc
    mixedMoment B raw17817 raw17817Labels = mixedMoment B raw17817step0 raw17817step0Labels := by
      have ha : raw17817step0 = (fun i j => raw17817 (permutation569 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17817step0 raw17817; decide +kernel
      have hl : raw17817step0Labels = raw17817Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17817 raw17817Labels permutation569 permutation5
    mixedMoment B raw17817step0 raw17817step0Labels = mixedMoment B raw17817step1 raw17817step1Labels := by
      have ha : raw17817step1 = raw17817step0 := by apply Matrix.ext; unfold raw17817step1 raw17817step0; decide +kernel
      have hl : raw17817step0Labels = labelEmbedding8 ∘ raw17817step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17817step0 raw17817step0Labels raw17817step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5197 node5197Labels := by rfl

def raw17818 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17818step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17818step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17818 raw17818Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw17818 raw17818Labels = mixedMoment B raw17818step0 raw17818step0Labels := by
      have hz : ∀ j, raw17818 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17818step0 = (fun i j => raw17818 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17818step0 raw17818; decide +kernel
      have hl : raw17818step0Labels = raw17818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17818 raw17818Labels permutation346 hz
    mixedMoment B raw17818step0 raw17818step0Labels = mixedMoment B raw17818step1 raw17818step1Labels := by
      have ha : raw17818step1 = (fun i j => raw17818step0 (permutation122 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17818step1 raw17818step0; decide +kernel
      have hl : raw17818step1Labels = raw17818step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17818step0 raw17818step0Labels permutation122 permutation5
    mixedMoment B raw17818step1 raw17818step1Labels = mixedMoment B raw17818step2 raw17818step2Labels := by
      have ha : raw17818step2 = raw17818step1 := by apply Matrix.ext; unfold raw17818step2 raw17818step1; decide +kernel
      have hl : raw17818step1Labels = labelEmbedding8 ∘ raw17818step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17818step1 raw17818step1Labels raw17818step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5198 node5198Labels := by rfl

def raw17819 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw17819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw17819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17819step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17819step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17819 raw17819Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw17819 raw17819Labels = mixedMoment B raw17819step0 raw17819step0Labels := by
      have hz : ∀ j, raw17819 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17819step0 = (fun i j => raw17819 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17819step0 raw17819; decide +kernel
      have hl : raw17819step0Labels = raw17819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17819 raw17819Labels permutation346 hz
    mixedMoment B raw17819step0 raw17819step0Labels = mixedMoment B raw17819step1 raw17819step1Labels := by
      have ha : raw17819step1 = (fun i j => raw17819step0 (permutation122 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17819step1 raw17819step0; decide +kernel
      have hl : raw17819step1Labels = raw17819step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17819step0 raw17819step0Labels permutation122 permutation5
    mixedMoment B raw17819step1 raw17819step1Labels = mixedMoment B raw17819step2 raw17819step2Labels := by
      have ha : raw17819step2 = raw17819step1 := by apply Matrix.ext; unfold raw17819step2 raw17819step1; decide +kernel
      have hl : raw17819step1Labels = labelEmbedding8 ∘ raw17819step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17819step1 raw17819step1Labels raw17819step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw17820 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17820step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17820step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17820 raw17820Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw17820 raw17820Labels = mixedMoment B raw17820step0 raw17820step0Labels := by
      have hz : ∀ j, raw17820 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17820step0 = (fun i j => raw17820 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17820step0 raw17820; decide +kernel
      have hl : raw17820step0Labels = raw17820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17820 raw17820Labels permutation346 hz
    mixedMoment B raw17820step0 raw17820step0Labels = mixedMoment B raw17820step1 raw17820step1Labels := by
      have ha : raw17820step1 = (fun i j => raw17820step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17820step1 raw17820step0; decide +kernel
      have hl : raw17820step1Labels = raw17820step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17820step0 raw17820step0Labels permutation151 permutation4
    mixedMoment B raw17820step1 raw17820step1Labels = mixedMoment B raw17820step2 raw17820step2Labels := by
      have ha : raw17820step2 = raw17820step1 := by apply Matrix.ext; unfold raw17820step2 raw17820step1; decide +kernel
      have hl : raw17820step1Labels = labelEmbedding7 ∘ raw17820step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17820step1 raw17820step1Labels raw17820step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw17821 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17821step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17821step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17821step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17821 raw17821Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw17821 raw17821Labels = mixedMoment B raw17821step0 raw17821step0Labels := by
      have hz : ∀ j, raw17821 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17821step0 = (fun i j => raw17821 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17821step0 raw17821; decide +kernel
      have hl : raw17821step0Labels = raw17821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17821 raw17821Labels permutation346 hz
    mixedMoment B raw17821step0 raw17821step0Labels = mixedMoment B raw17821step1 raw17821step1Labels := by
      have ha : raw17821step1 = (fun i j => raw17821step0 (permutation150 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17821step1 raw17821step0; decide +kernel
      have hl : raw17821step1Labels = raw17821step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17821step0 raw17821step0Labels permutation150 permutation4
    mixedMoment B raw17821step1 raw17821step1Labels = mixedMoment B raw17821step2 raw17821step2Labels := by
      have ha : raw17821step2 = raw17821step1 := by apply Matrix.ext; unfold raw17821step2 raw17821step1; decide +kernel
      have hl : raw17821step1Labels = labelEmbedding7 ∘ raw17821step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17821step1 raw17821step1Labels raw17821step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw17822 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17822step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17822step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17822 raw17822Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw17822 raw17822Labels = mixedMoment B raw17822step0 raw17822step0Labels := by
      have ha : raw17822step0 = (fun i j => raw17822 (permutation682 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17822step0 raw17822; decide +kernel
      have hl : raw17822step0Labels = raw17822Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17822 raw17822Labels permutation682 permutation4
    mixedMoment B raw17822step0 raw17822step0Labels = mixedMoment B raw17822step1 raw17822step1Labels := by
      have ha : raw17822step1 = raw17822step0 := by apply Matrix.ext; unfold raw17822step1 raw17822step0; decide +kernel
      have hl : raw17822step0Labels = labelEmbedding7 ∘ raw17822step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17822step0 raw17822step0Labels raw17822step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5365 node5365Labels := by rfl

def raw17823 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17823step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17823step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17823step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17823step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17823 raw17823Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw17823 raw17823Labels = mixedMoment B raw17823step0 raw17823step0Labels := by
      have hz : ∀ j, raw17823 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17823step0 = (fun i j => raw17823 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17823step0 raw17823; decide +kernel
      have hl : raw17823step0Labels = raw17823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17823 raw17823Labels permutation346 hz
    mixedMoment B raw17823step0 raw17823step0Labels = mixedMoment B raw17823step1 raw17823step1Labels := by
      have ha : raw17823step1 = (fun i j => raw17823step0 (permutation148 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17823step1 raw17823step0; decide +kernel
      have hl : raw17823step1Labels = raw17823step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17823step0 raw17823step0Labels permutation148 permutation4
    mixedMoment B raw17823step1 raw17823step1Labels = mixedMoment B raw17823step2 raw17823step2Labels := by
      have ha : raw17823step2 = raw17823step1 := by apply Matrix.ext; unfold raw17823step2 raw17823step1; decide +kernel
      have hl : raw17823step1Labels = labelEmbedding7 ∘ raw17823step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17823step1 raw17823step1Labels raw17823step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw17824 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17824Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17824step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17824step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17824step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17824 raw17824Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw17824 raw17824Labels = mixedMoment B raw17824step0 raw17824step0Labels := by
      have hz : ∀ j, raw17824 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17824step0 = (fun i j => raw17824 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17824step0 raw17824; decide +kernel
      have hl : raw17824step0Labels = raw17824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17824 raw17824Labels permutation346 hz
    mixedMoment B raw17824step0 raw17824step0Labels = mixedMoment B raw17824step1 raw17824step1Labels := by
      have ha : raw17824step1 = (fun i j => raw17824step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17824step1 raw17824step0; decide +kernel
      have hl : raw17824step1Labels = raw17824step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17824step0 raw17824step0Labels permutation151 permutation6
    mixedMoment B raw17824step1 raw17824step1Labels = mixedMoment B raw17824step2 raw17824step2Labels := by
      have ha : raw17824step2 = -raw17824step1 := by apply Matrix.ext; change ∀ i j, raw17824step2 i j = -(raw17824step1 i j); unfold raw17824step2 raw17824step1; decide +kernel
      have hl : raw17824step2Labels = raw17824step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw17825 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17825Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17825step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17825step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17825step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17825 raw17825Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw17825 raw17825Labels = mixedMoment B raw17825step0 raw17825step0Labels := by
      have ha : raw17825step0 = (fun i j => raw17825 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17825step0 raw17825; decide +kernel
      have hl : raw17825step0Labels = raw17825Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17825 raw17825Labels permutation682 permutation6
    mixedMoment B raw17825step0 raw17825step0Labels = mixedMoment B raw17825step1 raw17825step1Labels := by
      have ha : raw17825step1 = -raw17825step0 := by apply Matrix.ext; change ∀ i j, raw17825step1 i j = -(raw17825step0 i j); unfold raw17825step1 raw17825step0; decide +kernel
      have hl : raw17825step1Labels = raw17825step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3954 node3954Labels := by rfl

def raw17826 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17826Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17826step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17826step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17826 raw17826Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw17826 raw17826Labels = mixedMoment B raw17826step0 raw17826step0Labels := by
      have hz : ∀ j, raw17826 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17826step0 = (fun i j => raw17826 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17826step0 raw17826; decide +kernel
      have hl : raw17826step0Labels = raw17826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17826 raw17826Labels permutation346 hz
    mixedMoment B raw17826step0 raw17826step0Labels = mixedMoment B raw17826step1 raw17826step1Labels := by
      have ha : raw17826step1 = (fun i j => raw17826step0 (permutation101 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17826step1 raw17826step0; decide +kernel
      have hl : raw17826step1Labels = raw17826step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17826step0 raw17826step0Labels permutation101 permutation3
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw17827 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17827Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17827step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17827step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17827step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17827step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17827 raw17827Labels = mixedMoment B node4027 node4027Labels := by
  calc
    mixedMoment B raw17827 raw17827Labels = mixedMoment B raw17827step0 raw17827step0Labels := by
      have hz : ∀ j, raw17827 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17827step0 = (fun i j => raw17827 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17827step0 raw17827; decide +kernel
      have hl : raw17827step0Labels = raw17827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17827 raw17827Labels permutation346 hz
    mixedMoment B raw17827step0 raw17827step0Labels = mixedMoment B raw17827step1 raw17827step1Labels := by
      have ha : raw17827step1 = (fun i j => raw17827step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17827step1 raw17827step0; decide +kernel
      have hl : raw17827step1Labels = raw17827step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17827step0 raw17827step0Labels permutation44 permutation3
    mixedMoment B raw17827step1 raw17827step1Labels = mixedMoment B raw17827step2 raw17827step2Labels := by
      have ha : raw17827step2 = -raw17827step1 := by apply Matrix.ext; change ∀ i j, raw17827step2 i j = -(raw17827step1 i j); unfold raw17827step2 raw17827step1; decide +kernel
      have hl : raw17827step2Labels = raw17827step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4027 node4027Labels := by rfl

def raw17828 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17828Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17828step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17828step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17828 raw17828Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw17828 raw17828Labels = mixedMoment B raw17828step0 raw17828step0Labels := by
      have hz : ∀ j, raw17828 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17828step0 = (fun i j => raw17828 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17828step0 raw17828; decide +kernel
      have hl : raw17828step0Labels = raw17828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17828 raw17828Labels permutation346 hz
    mixedMoment B raw17828step0 raw17828step0Labels = mixedMoment B raw17828step1 raw17828step1Labels := by
      have ha : raw17828step1 = (fun i j => raw17828step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17828step1 raw17828step0; decide +kernel
      have hl : raw17828step1Labels = raw17828step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17828step0 raw17828step0Labels permutation32 permutation6
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw17829 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17829Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17829step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17829step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17829 raw17829Labels = mixedMoment B node3953 node3953Labels := by
  calc
    mixedMoment B raw17829 raw17829Labels = mixedMoment B raw17829step0 raw17829step0Labels := by
      have ha : raw17829step0 = (fun i j => raw17829 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17829step0 raw17829; decide +kernel
      have hl : raw17829step0Labels = raw17829Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17829 raw17829Labels permutation682 permutation6
    mixedMoment B raw17829step0 raw17829step0Labels = mixedMoment B raw17829step1 raw17829step1Labels := by
      have ha : raw17829step1 = -raw17829step0 := by apply Matrix.ext; change ∀ i j, raw17829step1 i j = -(raw17829step0 i j); unfold raw17829step1 raw17829step0; decide +kernel
      have hl : raw17829step1Labels = raw17829step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3953 node3953Labels := by rfl

def raw17830 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17830Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17830step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17830step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17830 raw17830Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw17830 raw17830Labels = mixedMoment B raw17830step0 raw17830step0Labels := by
      have hz : ∀ j, raw17830 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17830step0 = (fun i j => raw17830 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17830step0 raw17830; decide +kernel
      have hl : raw17830step0Labels = raw17830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17830 raw17830Labels permutation346 hz
    mixedMoment B raw17830step0 raw17830step0Labels = mixedMoment B raw17830step1 raw17830step1Labels := by
      have ha : raw17830step1 = (fun i j => raw17830step0 (permutation98 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17830step1 raw17830step0; decide +kernel
      have hl : raw17830step1Labels = raw17830step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17830step0 raw17830step0Labels permutation98 permutation3
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw17831 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17831Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17831step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17831step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17831 raw17831Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw17831 raw17831Labels = mixedMoment B raw17831step0 raw17831step0Labels := by
      have hz : ∀ j, raw17831 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17831step0 = (fun i j => raw17831 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17831step0 raw17831; decide +kernel
      have hl : raw17831step0Labels = raw17831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17831 raw17831Labels permutation346 hz
    mixedMoment B raw17831step0 raw17831step0Labels = mixedMoment B raw17831step1 raw17831step1Labels := by
      have ha : raw17831step1 = (fun i j => raw17831step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17831step1 raw17831step0; decide +kernel
      have hl : raw17831step1Labels = raw17831step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17831step0 raw17831step0Labels permutation32 permutation6
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw17832 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17832Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17832step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17832step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![-1, -1, 2]]
def raw17832step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17832step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17832step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17832 raw17832Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw17832 raw17832Labels = mixedMoment B raw17832step0 raw17832step0Labels := by
      have hz : ∀ j, raw17832 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17832step0 = (fun i j => raw17832 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17832step0 raw17832; decide +kernel
      have hl : raw17832step0Labels = raw17832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17832 raw17832Labels permutation434 hz
    mixedMoment B raw17832step0 raw17832step0Labels = mixedMoment B raw17832step1 raw17832step1Labels := by
      have hz : ∀ j, raw17832step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17832step1 = (fun i j => raw17832step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17832step1 raw17832step0; decide +kernel
      have hl : raw17832step1Labels = raw17832step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17832step0 raw17832step0Labels permutation80 hz
    mixedMoment B raw17832step1 raw17832step1Labels = mixedMoment B raw17832step2 raw17832step2Labels := by
      have ha : raw17832step2 = (fun i j => raw17832step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17832step2 raw17832step1; decide +kernel
      have hl : raw17832step2Labels = raw17832step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17832step1 raw17832step1Labels permutation8 permutation6
    _ = mixedMoment B node3817 node3817Labels := by rfl

def raw17833 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17833Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17833step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17833step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -2, 1], ![-1, -1, 2]]
def raw17833step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17833step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17833step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17833 raw17833Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw17833 raw17833Labels = mixedMoment B raw17833step0 raw17833step0Labels := by
      have hz : ∀ j, raw17833 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17833step0 = (fun i j => raw17833 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17833step0 raw17833; decide +kernel
      have hl : raw17833step0Labels = raw17833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17833 raw17833Labels permutation434 hz
    mixedMoment B raw17833step0 raw17833step0Labels = mixedMoment B raw17833step1 raw17833step1Labels := by
      have hz : ∀ j, raw17833step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17833step1 = (fun i j => raw17833step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17833step1 raw17833step0; decide +kernel
      have hl : raw17833step1Labels = raw17833step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17833step0 raw17833step0Labels permutation80 hz
    mixedMoment B raw17833step1 raw17833step1Labels = mixedMoment B raw17833step2 raw17833step2Labels := by
      have ha : raw17833step2 = (fun i j => raw17833step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17833step2 raw17833step1; decide +kernel
      have hl : raw17833step2Labels = raw17833step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17833step1 raw17833step1Labels permutation8 permutation6
    _ = mixedMoment B node3963 node3963Labels := by rfl

def raw17834 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17834Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17834step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17834step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17834step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17834step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17834 raw17834Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw17834 raw17834Labels = mixedMoment B raw17834step0 raw17834step0Labels := by
      have hz : ∀ j, raw17834 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17834step0 = (fun i j => raw17834 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17834step0 raw17834; decide +kernel
      have hl : raw17834step0Labels = raw17834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17834 raw17834Labels permutation434 hz
    mixedMoment B raw17834step0 raw17834step0Labels = mixedMoment B raw17834step1 raw17834step1Labels := by
      have ha : raw17834step1 = (fun i j => raw17834step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17834step1 raw17834step0; decide +kernel
      have hl : raw17834step1Labels = raw17834step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17834step0 raw17834step0Labels permutation151 permutation6
    mixedMoment B raw17834step1 raw17834step1Labels = mixedMoment B raw17834step2 raw17834step2Labels := by
      have ha : raw17834step2 = -raw17834step1 := by apply Matrix.ext; change ∀ i j, raw17834step2 i j = -(raw17834step1 i j); unfold raw17834step2 raw17834step1; decide +kernel
      have hl : raw17834step2Labels = raw17834step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw17835 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17835Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17835step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17835step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -2, 1], ![-2, 0, 2]]
def raw17835step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17835step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17835step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17835 raw17835Labels = mixedMoment B node3987 node3987Labels := by
  calc
    mixedMoment B raw17835 raw17835Labels = mixedMoment B raw17835step0 raw17835step0Labels := by
      have hz : ∀ j, raw17835 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17835step0 = (fun i j => raw17835 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17835step0 raw17835; decide +kernel
      have hl : raw17835step0Labels = raw17835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17835 raw17835Labels permutation434 hz
    mixedMoment B raw17835step0 raw17835step0Labels = mixedMoment B raw17835step1 raw17835step1Labels := by
      have hz : ∀ j, raw17835step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17835step1 = (fun i j => raw17835step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17835step1 raw17835step0; decide +kernel
      have hl : raw17835step1Labels = raw17835step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17835step0 raw17835step0Labels permutation80 hz
    mixedMoment B raw17835step1 raw17835step1Labels = mixedMoment B raw17835step2 raw17835step2Labels := by
      have ha : raw17835step2 = (fun i j => raw17835step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17835step2 raw17835step1; decide +kernel
      have hl : raw17835step2Labels = raw17835step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17835step1 raw17835step1Labels permutation8 permutation6
    _ = mixedMoment B node3987 node3987Labels := by rfl

def raw17836 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17836Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17836step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw17836step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17836step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw17836step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17836 raw17836Labels = mixedMoment B node3624 node3624Labels := by
  calc
    mixedMoment B raw17836 raw17836Labels = mixedMoment B raw17836step0 raw17836step0Labels := by
      have hz : ∀ j, raw17836 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17836step0 = (fun i j => raw17836 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17836step0 raw17836; decide +kernel
      have hl : raw17836step0Labels = raw17836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17836 raw17836Labels permutation346 hz
    mixedMoment B raw17836step0 raw17836step0Labels = mixedMoment B raw17836step1 raw17836step1Labels := by
      have ha : raw17836step1 = (fun i j => raw17836step0 (permutation111 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17836step1 raw17836step0; decide +kernel
      have hl : raw17836step1Labels = raw17836step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17836step0 raw17836step0Labels permutation111 permutation3
    mixedMoment B raw17836step1 raw17836step1Labels = mixedMoment B raw17836step2 raw17836step2Labels := by
      have ha : raw17836step2 = -raw17836step1 := by apply Matrix.ext; change ∀ i j, raw17836step2 i j = -(raw17836step1 i j); unfold raw17836step2 raw17836step1; decide +kernel
      have hl : raw17836step2Labels = raw17836step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3624 node3624Labels := by rfl

def raw17837 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17837Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17837step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17837step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw17837step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17837step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17837step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17837 raw17837Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw17837 raw17837Labels = mixedMoment B raw17837step0 raw17837step0Labels := by
      have hz : ∀ j, raw17837 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17837step0 = (fun i j => raw17837 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17837step0 raw17837; decide +kernel
      have hl : raw17837step0Labels = raw17837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17837 raw17837Labels permutation346 hz
    mixedMoment B raw17837step0 raw17837step0Labels = mixedMoment B raw17837step1 raw17837step1Labels := by
      have ha : raw17837step1 = (fun i j => raw17837step0 (permutation109 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17837step1 raw17837step0; decide +kernel
      have hl : raw17837step1Labels = raw17837step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17837step0 raw17837step0Labels permutation109 permutation3
    mixedMoment B raw17837step1 raw17837step1Labels = mixedMoment B raw17837step2 raw17837step2Labels := by
      have ha : raw17837step2 = -raw17837step1 := by apply Matrix.ext; change ∀ i j, raw17837step2 i j = -(raw17837step1 i j); unfold raw17837step2 raw17837step1; decide +kernel
      have hl : raw17837step2Labels = raw17837step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3578 node3578Labels := by rfl

def raw17838 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17838Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17838step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17838step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17838step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17838step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17838 raw17838Labels = mixedMoment B node3569 node3569Labels := by
  calc
    mixedMoment B raw17838 raw17838Labels = mixedMoment B raw17838step0 raw17838step0Labels := by
      have ha : raw17838step0 = (fun i j => raw17838 (permutation524 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17838step0 raw17838; decide +kernel
      have hl : raw17838step0Labels = raw17838Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17838 raw17838Labels permutation524 permutation3
    mixedMoment B raw17838step0 raw17838step0Labels = mixedMoment B raw17838step1 raw17838step1Labels := by
      have ha : raw17838step1 = -raw17838step0 := by apply Matrix.ext; change ∀ i j, raw17838step1 i j = -(raw17838step0 i j); unfold raw17838step1 raw17838step0; decide +kernel
      have hl : raw17838step1Labels = raw17838step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3569 node3569Labels := by rfl

def raw17839 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17839Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![2, -3, 1], ![-1, -1, 2]]
def raw17839step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw17839step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17839step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17839step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17839 raw17839Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw17839 raw17839Labels = mixedMoment B raw17839step0 raw17839step0Labels := by
      have hz : ∀ j, raw17839 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17839step0 = (fun i j => raw17839 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17839step0 raw17839; decide +kernel
      have hl : raw17839step0Labels = raw17839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17839 raw17839Labels permutation346 hz
    mixedMoment B raw17839step0 raw17839step0Labels = mixedMoment B raw17839step1 raw17839step1Labels := by
      have ha : raw17839step1 = (fun i j => raw17839step0 (permutation105 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17839step1 raw17839step0; decide +kernel
      have hl : raw17839step1Labels = raw17839step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17839step0 raw17839step0Labels permutation105 permutation3
    mixedMoment B raw17839step1 raw17839step1Labels = mixedMoment B raw17839step2 raw17839step2Labels := by
      have ha : raw17839step2 = -raw17839step1 := by apply Matrix.ext; change ∀ i j, raw17839step2 i j = -(raw17839step1 i j); unfold raw17839step2 raw17839step1; decide +kernel
      have hl : raw17839step2Labels = raw17839step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3570 node3570Labels := by rfl

def raw17840 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw17840Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw17840step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17840step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17840step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17840 raw17840Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw17840 raw17840Labels = mixedMoment B raw17840step0 raw17840step0Labels := by
      have hz : ∀ j, raw17840 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17840step0 = (fun i j => raw17840 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17840step0 raw17840; decide +kernel
      have hl : raw17840step0Labels = raw17840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17840 raw17840Labels permutation346 hz
    mixedMoment B raw17840step0 raw17840step0Labels = mixedMoment B raw17840step1 raw17840step1Labels := by
      have ha : raw17840step1 = (fun i j => raw17840step0 (permutation104 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17840step1 raw17840step0; decide +kernel
      have hl : raw17840step1Labels = raw17840step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17840step0 raw17840step0Labels permutation104 permutation3
    mixedMoment B raw17840step1 raw17840step1Labels = mixedMoment B raw17840step2 raw17840step2Labels := by
      have ha : raw17840step2 = -raw17840step1 := by apply Matrix.ext; change ∀ i j, raw17840step2 i j = -(raw17840step1 i j); unfold raw17840step2 raw17840step1; decide +kernel
      have hl : raw17840step2Labels = raw17840step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw17841 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17841Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17841step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw17841step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17841step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw17841step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17841 raw17841Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw17841 raw17841Labels = mixedMoment B raw17841step0 raw17841step0Labels := by
      have hz : ∀ j, raw17841 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17841step0 = (fun i j => raw17841 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17841step0 raw17841; decide +kernel
      have hl : raw17841step0Labels = raw17841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17841 raw17841Labels permutation346 hz
    mixedMoment B raw17841step0 raw17841step0Labels = mixedMoment B raw17841step1 raw17841step1Labels := by
      have ha : raw17841step1 = (fun i j => raw17841step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17841step1 raw17841step0; decide +kernel
      have hl : raw17841step1Labels = raw17841step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17841step0 raw17841step0Labels permutation151 permutation6
    mixedMoment B raw17841step1 raw17841step1Labels = mixedMoment B raw17841step2 raw17841step2Labels := by
      have ha : raw17841step2 = -raw17841step1 := by apply Matrix.ext; change ∀ i j, raw17841step2 i j = -(raw17841step1 i j); unfold raw17841step2 raw17841step1; decide +kernel
      have hl : raw17841step2Labels = raw17841step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3766 node3766Labels := by rfl

def raw17842 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17842Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17842step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17842step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17842step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17842step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17842 raw17842Labels = mixedMoment B node3767 node3767Labels := by
  calc
    mixedMoment B raw17842 raw17842Labels = mixedMoment B raw17842step0 raw17842step0Labels := by
      have hz : ∀ j, raw17842 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17842step0 = (fun i j => raw17842 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17842step0 raw17842; decide +kernel
      have hl : raw17842step0Labels = raw17842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17842 raw17842Labels permutation346 hz
    mixedMoment B raw17842step0 raw17842step0Labels = mixedMoment B raw17842step1 raw17842step1Labels := by
      have ha : raw17842step1 = (fun i j => raw17842step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17842step1 raw17842step0; decide +kernel
      have hl : raw17842step1Labels = raw17842step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17842step0 raw17842step0Labels permutation151 permutation6
    mixedMoment B raw17842step1 raw17842step1Labels = mixedMoment B raw17842step2 raw17842step2Labels := by
      have ha : raw17842step2 = -raw17842step1 := by apply Matrix.ext; change ∀ i j, raw17842step2 i j = -(raw17842step1 i j); unfold raw17842step2 raw17842step1; decide +kernel
      have hl : raw17842step2Labels = raw17842step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3767 node3767Labels := by rfl

def raw17843 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17843Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17843step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17843step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17843step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17843step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17843 raw17843Labels = mixedMoment B node3758 node3758Labels := by
  calc
    mixedMoment B raw17843 raw17843Labels = mixedMoment B raw17843step0 raw17843step0Labels := by
      have ha : raw17843step0 = (fun i j => raw17843 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17843step0 raw17843; decide +kernel
      have hl : raw17843step0Labels = raw17843Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17843 raw17843Labels permutation682 permutation6
    mixedMoment B raw17843step0 raw17843step0Labels = mixedMoment B raw17843step1 raw17843step1Labels := by
      have ha : raw17843step1 = -raw17843step0 := by apply Matrix.ext; change ∀ i j, raw17843step1 i j = -(raw17843step0 i j); unfold raw17843step1 raw17843step0; decide +kernel
      have hl : raw17843step1Labels = raw17843step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3758 node3758Labels := by rfl

def raw17844 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17844Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![1, -2, 1], ![0, -2, 2]]
def raw17844step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17844step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17844step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17844step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17844 raw17844Labels = mixedMoment B node3771 node3771Labels := by
  calc
    mixedMoment B raw17844 raw17844Labels = mixedMoment B raw17844step0 raw17844step0Labels := by
      have hz : ∀ j, raw17844 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17844step0 = (fun i j => raw17844 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17844step0 raw17844; decide +kernel
      have hl : raw17844step0Labels = raw17844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17844 raw17844Labels permutation346 hz
    mixedMoment B raw17844step0 raw17844step0Labels = mixedMoment B raw17844step1 raw17844step1Labels := by
      have ha : raw17844step1 = (fun i j => raw17844step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17844step1 raw17844step0; decide +kernel
      have hl : raw17844step1Labels = raw17844step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17844step0 raw17844step0Labels permutation151 permutation6
    mixedMoment B raw17844step1 raw17844step1Labels = mixedMoment B raw17844step2 raw17844step2Labels := by
      have ha : raw17844step2 = -raw17844step1 := by apply Matrix.ext; change ∀ i j, raw17844step2 i j = -(raw17844step1 i j); unfold raw17844step2 raw17844step1; decide +kernel
      have hl : raw17844step2Labels = raw17844step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3771 node3771Labels := by rfl

def raw17845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17845step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17845step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17845step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17845 raw17845Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw17845 raw17845Labels = mixedMoment B raw17845step0 raw17845step0Labels := by
      have hz : ∀ j, raw17845 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17845step0 = (fun i j => raw17845 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17845step0 raw17845; decide +kernel
      have hl : raw17845step0Labels = raw17845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17845 raw17845Labels permutation346 hz
    mixedMoment B raw17845step0 raw17845step0Labels = mixedMoment B raw17845step1 raw17845step1Labels := by
      have ha : raw17845step1 = (fun i j => raw17845step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17845step1 raw17845step0; decide +kernel
      have hl : raw17845step1Labels = raw17845step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17845step0 raw17845step0Labels permutation150 permutation2
    mixedMoment B raw17845step1 raw17845step1Labels = mixedMoment B raw17845step2 raw17845step2Labels := by
      have ha : raw17845step2 = -raw17845step1 := by apply Matrix.ext; change ∀ i j, raw17845step2 i j = -(raw17845step1 i j); unfold raw17845step2 raw17845step1; decide +kernel
      have hl : raw17845step2Labels = raw17845step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw17846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17846step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17846step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17846step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17846 raw17846Labels = mixedMoment B node5408 node5408Labels := by
  calc
    mixedMoment B raw17846 raw17846Labels = mixedMoment B raw17846step0 raw17846step0Labels := by
      have ha : raw17846step0 = (fun i j => raw17846 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17846step0 raw17846; decide +kernel
      have hl : raw17846step0Labels = raw17846Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17846 raw17846Labels permutation687 permutation2
    mixedMoment B raw17846step0 raw17846step0Labels = mixedMoment B raw17846step1 raw17846step1Labels := by
      have ha : raw17846step1 = -raw17846step0 := by apply Matrix.ext; change ∀ i j, raw17846step1 i j = -(raw17846step0 i j); unfold raw17846step1 raw17846step0; decide +kernel
      have hl : raw17846step1Labels = raw17846step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5408 node5408Labels := by rfl

def raw17847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17847step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw17847step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw17847step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw17847step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw17847step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw17847step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw17847step4 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw17847step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical17847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17847 raw17847Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw17847 raw17847Labels = mixedMoment B raw17847step0 raw17847step0Labels := by
      have hz : ∀ j, raw17847 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17847step0 = (fun i j => raw17847 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17847step0 raw17847; decide +kernel
      have hl : raw17847step0Labels = raw17847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17847 raw17847Labels permutation346 hz
    mixedMoment B raw17847step0 raw17847step0Labels = mixedMoment B raw17847step1 raw17847step1Labels := by
      have hz : ∀ i, raw17847step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw17847step1 = (fun i j => raw17847step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw17847step1 raw17847step0; decide +kernel
      have hl : raw17847step1Labels = (fun j => raw17847step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw17847step0 raw17847step0Labels permutation4 hz
    mixedMoment B raw17847step1 raw17847step1Labels = mixedMoment B raw17847step2 raw17847step2Labels := by
      have ha : raw17847step2 = (fun i j => raw17847step1 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw17847step2 raw17847step1; decide +kernel
      have hl : raw17847step2Labels = raw17847step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17847step1 raw17847step1Labels permutation146 permutation0
    mixedMoment B raw17847step2 raw17847step2Labels = mixedMoment B raw17847step3 raw17847step3Labels := by
      have ha : raw17847step3 = -raw17847step2 := by apply Matrix.ext; change ∀ i j, raw17847step3 i j = -(raw17847step2 i j); unfold raw17847step3 raw17847step2; decide +kernel
      have hl : raw17847step3Labels = raw17847step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17847step3 raw17847step3Labels = mixedMoment B raw17847step4 raw17847step4Labels := by
      have ha : raw17847step4 = raw17847step3 := by apply Matrix.ext; unfold raw17847step4 raw17847step3; decide +kernel
      have hl : raw17847step3Labels = labelEmbedding2 ∘ raw17847step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17847step3 raw17847step3Labels raw17847step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw17848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17848step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17848step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17848step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17848step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17848 raw17848Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw17848 raw17848Labels = mixedMoment B raw17848step0 raw17848step0Labels := by
      have hz : ∀ j, raw17848 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17848step0 = (fun i j => raw17848 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17848step0 raw17848; decide +kernel
      have hl : raw17848step0Labels = raw17848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17848 raw17848Labels permutation346 hz
    mixedMoment B raw17848step0 raw17848step0Labels = mixedMoment B raw17848step1 raw17848step1Labels := by
      have ha : raw17848step1 = (fun i j => raw17848step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17848step1 raw17848step0; decide +kernel
      have hl : raw17848step1Labels = raw17848step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17848step0 raw17848step0Labels permutation150 permutation7
    mixedMoment B raw17848step1 raw17848step1Labels = mixedMoment B raw17848step2 raw17848step2Labels := by
      have ha : raw17848step2 = raw17848step1 := by apply Matrix.ext; unfold raw17848step2 raw17848step1; decide +kernel
      have hl : raw17848step1Labels = labelEmbedding10 ∘ raw17848step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17848step1 raw17848step1Labels raw17848step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw17849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17849step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17849step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17849step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17849step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17849 raw17849Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw17849 raw17849Labels = mixedMoment B raw17849step0 raw17849step0Labels := by
      have hz : ∀ j, raw17849 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17849step0 = (fun i j => raw17849 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17849step0 raw17849; decide +kernel
      have hl : raw17849step0Labels = raw17849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17849 raw17849Labels permutation346 hz
    mixedMoment B raw17849step0 raw17849step0Labels = mixedMoment B raw17849step1 raw17849step1Labels := by
      have ha : raw17849step1 = (fun i j => raw17849step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17849step1 raw17849step0; decide +kernel
      have hl : raw17849step1Labels = raw17849step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17849step0 raw17849step0Labels permutation150 permutation7
    mixedMoment B raw17849step1 raw17849step1Labels = mixedMoment B raw17849step2 raw17849step2Labels := by
      have ha : raw17849step2 = raw17849step1 := by apply Matrix.ext; unfold raw17849step2 raw17849step1; decide +kernel
      have hl : raw17849step1Labels = labelEmbedding10 ∘ raw17849step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17849step1 raw17849step1Labels raw17849step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw17850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17850step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17850step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17850step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17850step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw17850step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17850 raw17850Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw17850 raw17850Labels = mixedMoment B raw17850step0 raw17850step0Labels := by
      have hz : ∀ j, raw17850 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17850step0 = (fun i j => raw17850 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17850step0 raw17850; decide +kernel
      have hl : raw17850step0Labels = raw17850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17850 raw17850Labels permutation346 hz
    mixedMoment B raw17850step0 raw17850step0Labels = mixedMoment B raw17850step1 raw17850step1Labels := by
      have ha : raw17850step1 = (fun i j => raw17850step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17850step1 raw17850step0; decide +kernel
      have hl : raw17850step1Labels = raw17850step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17850step0 raw17850step0Labels permutation32 permutation3
    mixedMoment B raw17850step1 raw17850step1Labels = mixedMoment B raw17850step2 raw17850step2Labels := by
      have ha : raw17850step2 = raw17850step1 := by apply Matrix.ext; unfold raw17850step2 raw17850step1; decide +kernel
      have hl : raw17850step1Labels = labelEmbedding6 ∘ raw17850step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17850step1 raw17850step1Labels raw17850step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw17851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17851step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17851step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17851step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17851 raw17851Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw17851 raw17851Labels = mixedMoment B raw17851step0 raw17851step0Labels := by
      have ha : raw17851step0 = (fun i j => raw17851 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17851step0 raw17851; decide +kernel
      have hl : raw17851step0Labels = raw17851Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17851 raw17851Labels permutation676 permutation2
    mixedMoment B raw17851step0 raw17851step0Labels = mixedMoment B raw17851step1 raw17851step1Labels := by
      have ha : raw17851step1 = -raw17851step0 := by apply Matrix.ext; change ∀ i j, raw17851step1 i j = -(raw17851step0 i j); unfold raw17851step1 raw17851step0; decide +kernel
      have hl : raw17851step1Labels = raw17851step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw17852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17852step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17852step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17852step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17852step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17852 raw17852Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw17852 raw17852Labels = mixedMoment B raw17852step0 raw17852step0Labels := by
      have hz : ∀ j, raw17852 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17852step0 = (fun i j => raw17852 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17852step0 raw17852; decide +kernel
      have hl : raw17852step0Labels = raw17852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17852 raw17852Labels permutation346 hz
    mixedMoment B raw17852step0 raw17852step0Labels = mixedMoment B raw17852step1 raw17852step1Labels := by
      have ha : raw17852step1 = (fun i j => raw17852step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17852step1 raw17852step0; decide +kernel
      have hl : raw17852step1Labels = raw17852step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17852step0 raw17852step0Labels permutation149 permutation2
    mixedMoment B raw17852step1 raw17852step1Labels = mixedMoment B raw17852step2 raw17852step2Labels := by
      have ha : raw17852step2 = -raw17852step1 := by apply Matrix.ext; change ∀ i j, raw17852step2 i j = -(raw17852step1 i j); unfold raw17852step2 raw17852step1; decide +kernel
      have hl : raw17852step2Labels = raw17852step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw17853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17853step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17853step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17853step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17853step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17853step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17853step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17853 raw17853Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw17853 raw17853Labels = mixedMoment B raw17853step0 raw17853step0Labels := by
      have hz : ∀ j, raw17853 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17853step0 = (fun i j => raw17853 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17853step0 raw17853; decide +kernel
      have hl : raw17853step0Labels = raw17853Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17853 raw17853Labels permutation346 hz
    mixedMoment B raw17853step0 raw17853step0Labels = mixedMoment B raw17853step1 raw17853step1Labels := by
      have ha : raw17853step1 = (fun i j => raw17853step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17853step1 raw17853step0; decide +kernel
      have hl : raw17853step1Labels = raw17853step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17853step0 raw17853step0Labels permutation149 permutation7
    mixedMoment B raw17853step1 raw17853step1Labels = mixedMoment B raw17853step2 raw17853step2Labels := by
      have ha : raw17853step2 = raw17853step1 := by apply Matrix.ext; unfold raw17853step2 raw17853step1; decide +kernel
      have hl : raw17853step1Labels = labelEmbedding10 ∘ raw17853step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17853step1 raw17853step1Labels raw17853step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw17854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17854step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17854step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17854step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17854step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17854step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17854 raw17854Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw17854 raw17854Labels = mixedMoment B raw17854step0 raw17854step0Labels := by
      have hz : ∀ j, raw17854 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17854step0 = (fun i j => raw17854 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17854step0 raw17854; decide +kernel
      have hl : raw17854step0Labels = raw17854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17854 raw17854Labels permutation346 hz
    mixedMoment B raw17854step0 raw17854step0Labels = mixedMoment B raw17854step1 raw17854step1Labels := by
      have ha : raw17854step1 = (fun i j => raw17854step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17854step1 raw17854step0; decide +kernel
      have hl : raw17854step1Labels = raw17854step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17854step0 raw17854step0Labels permutation149 permutation7
    mixedMoment B raw17854step1 raw17854step1Labels = mixedMoment B raw17854step2 raw17854step2Labels := by
      have ha : raw17854step2 = raw17854step1 := by apply Matrix.ext; unfold raw17854step2 raw17854step1; decide +kernel
      have hl : raw17854step1Labels = labelEmbedding10 ∘ raw17854step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17854step1 raw17854step1Labels raw17854step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw17855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17855step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17855step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17855step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17855 raw17855Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw17855 raw17855Labels = mixedMoment B raw17855step0 raw17855step0Labels := by
      have ha : raw17855step0 = (fun i j => raw17855 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17855step0 raw17855; decide +kernel
      have hl : raw17855step0Labels = raw17855Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17855 raw17855Labels permutation160 permutation3
    mixedMoment B raw17855step0 raw17855step0Labels = mixedMoment B raw17855step1 raw17855step1Labels := by
      have ha : raw17855step1 = raw17855step0 := by apply Matrix.ext; unfold raw17855step1 raw17855step0; decide +kernel
      have hl : raw17855step0Labels = labelEmbedding6 ∘ raw17855step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17855step0 raw17855step0Labels raw17855step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw17856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17856step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17856 raw17856Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw17856 raw17856Labels = mixedMoment B raw17856step0 raw17856step0Labels := by
      have ha : raw17856step0 = (fun i j => raw17856 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17856step0 raw17856; decide +kernel
      have hl : raw17856step0Labels = raw17856Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17856 raw17856Labels permutation681 permutation2
    mixedMoment B raw17856step0 raw17856step0Labels = mixedMoment B raw17856step1 raw17856step1Labels := by
      have ha : raw17856step1 = -raw17856step0 := by apply Matrix.ext; change ∀ i j, raw17856step1 i j = -(raw17856step0 i j); unfold raw17856step1 raw17856step0; decide +kernel
      have hl : raw17856step1Labels = raw17856step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw17857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17857step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17857step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17857 raw17857Labels = mixedMoment B node5396 node5396Labels := by
  calc
    mixedMoment B raw17857 raw17857Labels = mixedMoment B raw17857step0 raw17857step0Labels := by
      have ha : raw17857step0 = (fun i j => raw17857 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17857step0 raw17857; decide +kernel
      have hl : raw17857step0Labels = raw17857Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17857 raw17857Labels permutation680 permutation2
    mixedMoment B raw17857step0 raw17857step0Labels = mixedMoment B raw17857step1 raw17857step1Labels := by
      have ha : raw17857step1 = -raw17857step0 := by apply Matrix.ext; change ∀ i j, raw17857step1 i j = -(raw17857step0 i j); unfold raw17857step1 raw17857step0; decide +kernel
      have hl : raw17857step1Labels = raw17857step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5396 node5396Labels := by rfl

def raw17858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17858step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17858step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17858step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17858 raw17858Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17858 raw17858Labels = mixedMoment B raw17858step0 raw17858step0Labels := by
      have ha : raw17858step0 = (fun i j => raw17858 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17858step0 raw17858; decide +kernel
      have hl : raw17858step0Labels = raw17858Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17858 raw17858Labels permutation646 permutation2
    mixedMoment B raw17858step0 raw17858step0Labels = mixedMoment B raw17858step1 raw17858step1Labels := by
      have ha : raw17858step1 = -raw17858step0 := by apply Matrix.ext; change ∀ i j, raw17858step1 i j = -(raw17858step0 i j); unfold raw17858step1 raw17858step0; decide +kernel
      have hl : raw17858step1Labels = raw17858step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw17859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17859 raw17859Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw17859 raw17859Labels = mixedMoment B raw17859step0 raw17859step0Labels := by
      have ha : raw17859step0 = (fun i j => raw17859 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17859step0 raw17859; decide +kernel
      have hl : raw17859step0Labels = raw17859Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17859 raw17859Labels permutation158 permutation2
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw17860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17860step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17860step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17860step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17860 raw17860Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw17860 raw17860Labels = mixedMoment B raw17860step0 raw17860step0Labels := by
      have hz : ∀ j, raw17860 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17860step0 = (fun i j => raw17860 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17860step0 raw17860; decide +kernel
      have hl : raw17860step0Labels = raw17860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17860 raw17860Labels permutation346 hz
    mixedMoment B raw17860step0 raw17860step0Labels = mixedMoment B raw17860step1 raw17860step1Labels := by
      have ha : raw17860step1 = (fun i j => raw17860step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17860step1 raw17860step0; decide +kernel
      have hl : raw17860step1Labels = raw17860step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17860step0 raw17860step0Labels permutation34 permutation3
    mixedMoment B raw17860step1 raw17860step1Labels = mixedMoment B raw17860step2 raw17860step2Labels := by
      have ha : raw17860step2 = raw17860step1 := by apply Matrix.ext; unfold raw17860step2 raw17860step1; decide +kernel
      have hl : raw17860step1Labels = labelEmbedding6 ∘ raw17860step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17860step1 raw17860step1Labels raw17860step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw17861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17861step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17861step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17861 raw17861Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw17861 raw17861Labels = mixedMoment B raw17861step0 raw17861step0Labels := by
      have hz : ∀ j, raw17861 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17861step0 = (fun i j => raw17861 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17861step0 raw17861; decide +kernel
      have hl : raw17861step0Labels = raw17861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17861 raw17861Labels permutation346 hz
    mixedMoment B raw17861step0 raw17861step0Labels = mixedMoment B raw17861step1 raw17861step1Labels := by
      have ha : raw17861step1 = (fun i j => raw17861step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17861step1 raw17861step0; decide +kernel
      have hl : raw17861step1Labels = raw17861step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17861step0 raw17861step0Labels permutation150 permutation2
    mixedMoment B raw17861step1 raw17861step1Labels = mixedMoment B raw17861step2 raw17861step2Labels := by
      have ha : raw17861step2 = -raw17861step1 := by apply Matrix.ext; change ∀ i j, raw17861step2 i j = -(raw17861step1 i j); unfold raw17861step2 raw17861step1; decide +kernel
      have hl : raw17861step2Labels = raw17861step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw17862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17862step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17862step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17862 raw17862Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw17862 raw17862Labels = mixedMoment B raw17862step0 raw17862step0Labels := by
      have ha : raw17862step0 = (fun i j => raw17862 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17862step0 raw17862; decide +kernel
      have hl : raw17862step0Labels = raw17862Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17862 raw17862Labels permutation688 permutation2
    mixedMoment B raw17862step0 raw17862step0Labels = mixedMoment B raw17862step1 raw17862step1Labels := by
      have ha : raw17862step1 = -raw17862step0 := by apply Matrix.ext; change ∀ i j, raw17862step1 i j = -(raw17862step0 i j); unfold raw17862step1 raw17862step0; decide +kernel
      have hl : raw17862step1Labels = raw17862step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw17863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw17863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17863step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17863step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17863step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17863step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17863 raw17863Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw17863 raw17863Labels = mixedMoment B raw17863step0 raw17863step0Labels := by
      have hz : ∀ j, raw17863 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17863step0 = (fun i j => raw17863 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17863step0 raw17863; decide +kernel
      have hl : raw17863step0Labels = raw17863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17863 raw17863Labels permutation346 hz
    mixedMoment B raw17863step0 raw17863step0Labels = mixedMoment B raw17863step1 raw17863step1Labels := by
      have ha : raw17863step1 = (fun i j => raw17863step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17863step1 raw17863step0; decide +kernel
      have hl : raw17863step1Labels = raw17863step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17863step0 raw17863step0Labels permutation151 permutation7
    mixedMoment B raw17863step1 raw17863step1Labels = mixedMoment B raw17863step2 raw17863step2Labels := by
      have ha : raw17863step2 = raw17863step1 := by apply Matrix.ext; unfold raw17863step2 raw17863step1; decide +kernel
      have hl : raw17863step1Labels = labelEmbedding10 ∘ raw17863step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17863step1 raw17863step1Labels raw17863step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw17864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17864 raw17864Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw17864 raw17864Labels = mixedMoment B raw17864step0 raw17864step0Labels := by
      have hz : ∀ j, raw17864 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17864step0 = (fun i j => raw17864 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17864step0 raw17864; decide +kernel
      have hl : raw17864step0Labels = raw17864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17864 raw17864Labels permutation346 hz
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw17865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17865step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17865step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17865 raw17865Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw17865 raw17865Labels = mixedMoment B raw17865step0 raw17865step0Labels := by
      have hz : ∀ j, raw17865 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17865step0 = (fun i j => raw17865 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17865step0 raw17865; decide +kernel
      have hl : raw17865step0Labels = raw17865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17865 raw17865Labels permutation346 hz
    mixedMoment B raw17865step0 raw17865step0Labels = mixedMoment B raw17865step1 raw17865step1Labels := by
      have ha : raw17865step1 = (fun i j => raw17865step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17865step1 raw17865step0; decide +kernel
      have hl : raw17865step1Labels = raw17865step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17865step0 raw17865step0Labels permutation33 permutation3
    mixedMoment B raw17865step1 raw17865step1Labels = mixedMoment B raw17865step2 raw17865step2Labels := by
      have ha : raw17865step2 = raw17865step1 := by apply Matrix.ext; unfold raw17865step2 raw17865step1; decide +kernel
      have hl : raw17865step1Labels = labelEmbedding6 ∘ raw17865step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17865step1 raw17865step1Labels raw17865step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw17866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17866step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17866step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17866step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17866step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17866 raw17866Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw17866 raw17866Labels = mixedMoment B raw17866step0 raw17866step0Labels := by
      have hz : ∀ j, raw17866 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17866step0 = (fun i j => raw17866 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17866step0 raw17866; decide +kernel
      have hl : raw17866step0Labels = raw17866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17866 raw17866Labels permutation346 hz
    mixedMoment B raw17866step0 raw17866step0Labels = mixedMoment B raw17866step1 raw17866step1Labels := by
      have ha : raw17866step1 = (fun i j => raw17866step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17866step1 raw17866step0; decide +kernel
      have hl : raw17866step1Labels = raw17866step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17866step0 raw17866step0Labels permutation150 permutation2
    mixedMoment B raw17866step1 raw17866step1Labels = mixedMoment B raw17866step2 raw17866step2Labels := by
      have ha : raw17866step2 = -raw17866step1 := by apply Matrix.ext; change ∀ i j, raw17866step2 i j = -(raw17866step1 i j); unfold raw17866step2 raw17866step1; decide +kernel
      have hl : raw17866step2Labels = raw17866step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw17867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17867step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17867step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17867 raw17867Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw17867 raw17867Labels = mixedMoment B raw17867step0 raw17867step0Labels := by
      have ha : raw17867step0 = (fun i j => raw17867 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17867step0 raw17867; decide +kernel
      have hl : raw17867step0Labels = raw17867Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17867 raw17867Labels permutation688 permutation2
    mixedMoment B raw17867step0 raw17867step0Labels = mixedMoment B raw17867step1 raw17867step1Labels := by
      have ha : raw17867step1 = -raw17867step0 := by apply Matrix.ext; change ∀ i j, raw17867step1 i j = -(raw17867step0 i j); unfold raw17867step1 raw17867step0; decide +kernel
      have hl : raw17867step1Labels = raw17867step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw17868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17868step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17868step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17868step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17868 raw17868Labels = mixedMoment B node5369 node5369Labels := by
  calc
    mixedMoment B raw17868 raw17868Labels = mixedMoment B raw17868step0 raw17868step0Labels := by
      have hz : ∀ j, raw17868 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17868step0 = (fun i j => raw17868 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17868step0 raw17868; decide +kernel
      have hl : raw17868step0Labels = raw17868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17868 raw17868Labels permutation346 hz
    mixedMoment B raw17868step0 raw17868step0Labels = mixedMoment B raw17868step1 raw17868step1Labels := by
      have ha : raw17868step1 = (fun i j => raw17868step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17868step1 raw17868step0; decide +kernel
      have hl : raw17868step1Labels = raw17868step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17868step0 raw17868step0Labels permutation149 permutation2
    mixedMoment B raw17868step1 raw17868step1Labels = mixedMoment B raw17868step2 raw17868step2Labels := by
      have ha : raw17868step2 = -raw17868step1 := by apply Matrix.ext; change ∀ i j, raw17868step2 i j = -(raw17868step1 i j); unfold raw17868step2 raw17868step1; decide +kernel
      have hl : raw17868step2Labels = raw17868step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5369 node5369Labels := by rfl

def raw17869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw17869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw17869step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17869step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17869step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17869step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17869step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17869 raw17869Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw17869 raw17869Labels = mixedMoment B raw17869step0 raw17869step0Labels := by
      have hz : ∀ j, raw17869 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17869step0 = (fun i j => raw17869 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17869step0 raw17869; decide +kernel
      have hl : raw17869step0Labels = raw17869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17869 raw17869Labels permutation346 hz
    mixedMoment B raw17869step0 raw17869step0Labels = mixedMoment B raw17869step1 raw17869step1Labels := by
      have ha : raw17869step1 = (fun i j => raw17869step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17869step1 raw17869step0; decide +kernel
      have hl : raw17869step1Labels = raw17869step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17869step0 raw17869step0Labels permutation127 permutation2
    mixedMoment B raw17869step1 raw17869step1Labels = mixedMoment B raw17869step2 raw17869step2Labels := by
      have ha : raw17869step2 = -raw17869step1 := by apply Matrix.ext; change ∀ i j, raw17869step2 i j = -(raw17869step1 i j); unfold raw17869step2 raw17869step1; decide +kernel
      have hl : raw17869step2Labels = raw17869step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw17870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17870step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17870step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw17870step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17870step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw17870step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17870 raw17870Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw17870 raw17870Labels = mixedMoment B raw17870step0 raw17870step0Labels := by
      have hz : ∀ j, raw17870 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17870step0 = (fun i j => raw17870 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17870step0 raw17870; decide +kernel
      have hl : raw17870step0Labels = raw17870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17870 raw17870Labels permutation346 hz
    mixedMoment B raw17870step0 raw17870step0Labels = mixedMoment B raw17870step1 raw17870step1Labels := by
      have ha : raw17870step1 = (fun i j => raw17870step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17870step1 raw17870step0; decide +kernel
      have hl : raw17870step1Labels = raw17870step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17870step0 raw17870step0Labels permutation151 permutation2
    mixedMoment B raw17870step1 raw17870step1Labels = mixedMoment B raw17870step2 raw17870step2Labels := by
      have ha : raw17870step2 = -raw17870step1 := by apply Matrix.ext; change ∀ i j, raw17870step2 i j = -(raw17870step1 i j); unfold raw17870step2 raw17870step1; decide +kernel
      have hl : raw17870step2Labels = raw17870step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw17871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17871step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17871step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17871step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17871step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17871 raw17871Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw17871 raw17871Labels = mixedMoment B raw17871step0 raw17871step0Labels := by
      have hz : ∀ j, raw17871 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17871step0 = (fun i j => raw17871 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17871step0 raw17871; decide +kernel
      have hl : raw17871step0Labels = raw17871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17871 raw17871Labels permutation346 hz
    mixedMoment B raw17871step0 raw17871step0Labels = mixedMoment B raw17871step1 raw17871step1Labels := by
      have ha : raw17871step1 = (fun i j => raw17871step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17871step1 raw17871step0; decide +kernel
      have hl : raw17871step1Labels = raw17871step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17871step0 raw17871step0Labels permutation150 permutation2
    mixedMoment B raw17871step1 raw17871step1Labels = mixedMoment B raw17871step2 raw17871step2Labels := by
      have ha : raw17871step2 = -raw17871step1 := by apply Matrix.ext; change ∀ i j, raw17871step2 i j = -(raw17871step1 i j); unfold raw17871step2 raw17871step1; decide +kernel
      have hl : raw17871step2Labels = raw17871step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5081 node5081Labels := by rfl

def raw17872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17872step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17872step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17872step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17872 raw17872Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw17872 raw17872Labels = mixedMoment B raw17872step0 raw17872step0Labels := by
      have ha : raw17872step0 = (fun i j => raw17872 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17872step0 raw17872; decide +kernel
      have hl : raw17872step0Labels = raw17872Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17872 raw17872Labels permutation688 permutation2
    mixedMoment B raw17872step0 raw17872step0Labels = mixedMoment B raw17872step1 raw17872step1Labels := by
      have ha : raw17872step1 = -raw17872step0 := by apply Matrix.ext; change ∀ i j, raw17872step1 i j = -(raw17872step0 i j); unfold raw17872step1 raw17872step0; decide +kernel
      have hl : raw17872step1Labels = raw17872step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw17873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17873step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17873step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17873step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17873step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17873 raw17873Labels = mixedMoment B node5104 node5104Labels := by
  calc
    mixedMoment B raw17873 raw17873Labels = mixedMoment B raw17873step0 raw17873step0Labels := by
      have hz : ∀ j, raw17873 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17873step0 = (fun i j => raw17873 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17873step0 raw17873; decide +kernel
      have hl : raw17873step0Labels = raw17873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17873 raw17873Labels permutation346 hz
    mixedMoment B raw17873step0 raw17873step0Labels = mixedMoment B raw17873step1 raw17873step1Labels := by
      have ha : raw17873step1 = (fun i j => raw17873step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17873step1 raw17873step0; decide +kernel
      have hl : raw17873step1Labels = raw17873step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17873step0 raw17873step0Labels permutation149 permutation2
    mixedMoment B raw17873step1 raw17873step1Labels = mixedMoment B raw17873step2 raw17873step2Labels := by
      have ha : raw17873step2 = -raw17873step1 := by apply Matrix.ext; change ∀ i j, raw17873step2 i j = -(raw17873step1 i j); unfold raw17873step2 raw17873step1; decide +kernel
      have hl : raw17873step2Labels = raw17873step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5104 node5104Labels := by rfl

def raw17874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw17874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw17874step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17874step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17874step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17874step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17874 raw17874Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw17874 raw17874Labels = mixedMoment B raw17874step0 raw17874step0Labels := by
      have hz : ∀ j, raw17874 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17874step0 = (fun i j => raw17874 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17874step0 raw17874; decide +kernel
      have hl : raw17874step0Labels = raw17874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17874 raw17874Labels permutation346 hz
    mixedMoment B raw17874step0 raw17874step0Labels = mixedMoment B raw17874step1 raw17874step1Labels := by
      have ha : raw17874step1 = (fun i j => raw17874step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17874step1 raw17874step0; decide +kernel
      have hl : raw17874step1Labels = raw17874step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17874step0 raw17874step0Labels permutation151 permutation2
    mixedMoment B raw17874step1 raw17874step1Labels = mixedMoment B raw17874step2 raw17874step2Labels := by
      have ha : raw17874step2 = -raw17874step1 := by apply Matrix.ext; change ∀ i j, raw17874step2 i j = -(raw17874step1 i j); unfold raw17874step2 raw17874step1; decide +kernel
      have hl : raw17874step2Labels = raw17874step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw17875 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17875step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17875step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17875step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17875step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17875step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17875step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17875 raw17875Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw17875 raw17875Labels = mixedMoment B raw17875step0 raw17875step0Labels := by
      have hz : ∀ j, raw17875 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17875step0 = (fun i j => raw17875 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17875step0 raw17875; decide +kernel
      have hl : raw17875step0Labels = raw17875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17875 raw17875Labels permutation346 hz
    mixedMoment B raw17875step0 raw17875step0Labels = mixedMoment B raw17875step1 raw17875step1Labels := by
      have ha : raw17875step1 = (fun i j => raw17875step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17875step1 raw17875step0; decide +kernel
      have hl : raw17875step1Labels = raw17875step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17875step0 raw17875step0Labels permutation151 permutation6
    mixedMoment B raw17875step1 raw17875step1Labels = mixedMoment B raw17875step2 raw17875step2Labels := by
      have ha : raw17875step2 = -raw17875step1 := by apply Matrix.ext; change ∀ i j, raw17875step2 i j = -(raw17875step1 i j); unfold raw17875step2 raw17875step1; decide +kernel
      have hl : raw17875step2Labels = raw17875step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17875step2 raw17875step2Labels = mixedMoment B raw17875step3 raw17875step3Labels := by
      have ha : raw17875step3 = raw17875step2 := by apply Matrix.ext; unfold raw17875step3 raw17875step2; decide +kernel
      have hl : raw17875step2Labels = labelEmbedding9 ∘ raw17875step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17875step2 raw17875step2Labels raw17875step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw17876 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17876step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17876step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17876step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17876step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17876step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17876 raw17876Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw17876 raw17876Labels = mixedMoment B raw17876step0 raw17876step0Labels := by
      have ha : raw17876step0 = (fun i j => raw17876 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17876step0 raw17876; decide +kernel
      have hl : raw17876step0Labels = raw17876Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17876 raw17876Labels permutation682 permutation6
    mixedMoment B raw17876step0 raw17876step0Labels = mixedMoment B raw17876step1 raw17876step1Labels := by
      have ha : raw17876step1 = -raw17876step0 := by apply Matrix.ext; change ∀ i j, raw17876step1 i j = -(raw17876step0 i j); unfold raw17876step1 raw17876step0; decide +kernel
      have hl : raw17876step1Labels = raw17876step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17876step1 raw17876step1Labels = mixedMoment B raw17876step2 raw17876step2Labels := by
      have ha : raw17876step2 = raw17876step1 := by apply Matrix.ext; unfold raw17876step2 raw17876step1; decide +kernel
      have hl : raw17876step1Labels = labelEmbedding9 ∘ raw17876step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17876step1 raw17876step1Labels raw17876step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw17877 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17877step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17877step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17877step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17877step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17877 raw17877Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw17877 raw17877Labels = mixedMoment B raw17877step0 raw17877step0Labels := by
      have hz : ∀ j, raw17877 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17877step0 = (fun i j => raw17877 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17877step0 raw17877; decide +kernel
      have hl : raw17877step0Labels = raw17877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17877 raw17877Labels permutation346 hz
    mixedMoment B raw17877step0 raw17877step0Labels = mixedMoment B raw17877step1 raw17877step1Labels := by
      have ha : raw17877step1 = (fun i j => raw17877step0 (permutation146 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17877step1 raw17877step0; decide +kernel
      have hl : raw17877step1Labels = raw17877step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17877step0 raw17877step0Labels permutation146 permutation4
    mixedMoment B raw17877step1 raw17877step1Labels = mixedMoment B raw17877step2 raw17877step2Labels := by
      have ha : raw17877step2 = raw17877step1 := by apply Matrix.ext; unfold raw17877step2 raw17877step1; decide +kernel
      have hl : raw17877step1Labels = labelEmbedding7 ∘ raw17877step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17877step1 raw17877step1Labels raw17877step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw17878 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17878step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17878step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17878step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17878step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17878step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17878 raw17878Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw17878 raw17878Labels = mixedMoment B raw17878step0 raw17878step0Labels := by
      have hz : ∀ j, raw17878 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17878step0 = (fun i j => raw17878 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17878step0 raw17878; decide +kernel
      have hl : raw17878step0Labels = raw17878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17878 raw17878Labels permutation346 hz
    mixedMoment B raw17878step0 raw17878step0Labels = mixedMoment B raw17878step1 raw17878step1Labels := by
      have ha : raw17878step1 = (fun i j => raw17878step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17878step1 raw17878step0; decide +kernel
      have hl : raw17878step1Labels = raw17878step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17878step0 raw17878step0Labels permutation149 permutation4
    mixedMoment B raw17878step1 raw17878step1Labels = mixedMoment B raw17878step2 raw17878step2Labels := by
      have ha : raw17878step2 = raw17878step1 := by apply Matrix.ext; unfold raw17878step2 raw17878step1; decide +kernel
      have hl : raw17878step1Labels = labelEmbedding7 ∘ raw17878step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17878step1 raw17878step1Labels raw17878step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw17879 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17879step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17879step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17879step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17879step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17879step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17879 raw17879Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw17879 raw17879Labels = mixedMoment B raw17879step0 raw17879step0Labels := by
      have ha : raw17879step0 = (fun i j => raw17879 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17879step0 raw17879; decide +kernel
      have hl : raw17879step0Labels = raw17879Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17879 raw17879Labels permutation682 permutation6
    mixedMoment B raw17879step0 raw17879step0Labels = mixedMoment B raw17879step1 raw17879step1Labels := by
      have ha : raw17879step1 = -raw17879step0 := by apply Matrix.ext; change ∀ i j, raw17879step1 i j = -(raw17879step0 i j); unfold raw17879step1 raw17879step0; decide +kernel
      have hl : raw17879step1Labels = raw17879step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17879step1 raw17879step1Labels = mixedMoment B raw17879step2 raw17879step2Labels := by
      have ha : raw17879step2 = raw17879step1 := by apply Matrix.ext; unfold raw17879step2 raw17879step1; decide +kernel
      have hl : raw17879step1Labels = labelEmbedding9 ∘ raw17879step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17879step1 raw17879step1Labels raw17879step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw17880 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17880step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17880step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17880 raw17880Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw17880 raw17880Labels = mixedMoment B raw17880step0 raw17880step0Labels := by
      have hz : ∀ j, raw17880 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17880step0 = (fun i j => raw17880 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17880step0 raw17880; decide +kernel
      have hl : raw17880step0Labels = raw17880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17880 raw17880Labels permutation346 hz
    mixedMoment B raw17880step0 raw17880step0Labels = mixedMoment B raw17880step1 raw17880step1Labels := by
      have ha : raw17880step1 = (fun i j => raw17880step0 (permutation148 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17880step1 raw17880step0; decide +kernel
      have hl : raw17880step1Labels = raw17880step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17880step0 raw17880step0Labels permutation148 permutation4
    mixedMoment B raw17880step1 raw17880step1Labels = mixedMoment B raw17880step2 raw17880step2Labels := by
      have ha : raw17880step2 = raw17880step1 := by apply Matrix.ext; unfold raw17880step2 raw17880step1; decide +kernel
      have hl : raw17880step1Labels = labelEmbedding7 ∘ raw17880step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17880step1 raw17880step1Labels raw17880step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw17881 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17881step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2]]
def raw17881step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17881step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-2, 2]]
def raw17881step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw17881step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw17881step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw17881step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw17881step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical17881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17881 raw17881Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw17881 raw17881Labels = mixedMoment B raw17881step0 raw17881step0Labels := by
      have hz : ∀ j, raw17881 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17881step0 = (fun i j => raw17881 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17881step0 raw17881; decide +kernel
      have hl : raw17881step0Labels = raw17881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17881 raw17881Labels permutation434 hz
    mixedMoment B raw17881step0 raw17881step0Labels = mixedMoment B raw17881step1 raw17881step1Labels := by
      have hz : ∀ j, raw17881step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17881step1 = (fun i j => raw17881step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17881step1 raw17881step0; decide +kernel
      have hl : raw17881step1Labels = raw17881step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17881step0 raw17881step0Labels permutation80 hz
    mixedMoment B raw17881step1 raw17881step1Labels = mixedMoment B raw17881step2 raw17881step2Labels := by
      have hz : ∀ i, raw17881step1 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw17881step2 = (fun i j => raw17881step1 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw17881step2 raw17881step1; decide +kernel
      have hl : raw17881step2Labels = (fun j => raw17881step1Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw17881step1 raw17881step1Labels permutation2 hz
    mixedMoment B raw17881step2 raw17881step2Labels = mixedMoment B raw17881step3 raw17881step3Labels := by
      have ha : raw17881step3 = (fun i j => raw17881step2 (permutation31 i) (permutation0 j)) := by apply Matrix.ext; unfold raw17881step3 raw17881step2; decide +kernel
      have hl : raw17881step3Labels = raw17881step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17881step2 raw17881step2Labels permutation31 permutation0
    mixedMoment B raw17881step3 raw17881step3Labels = mixedMoment B raw17881step4 raw17881step4Labels := by
      have ha : raw17881step4 = raw17881step3 := by apply Matrix.ext; unfold raw17881step4 raw17881step3; decide +kernel
      have hl : raw17881step3Labels = labelEmbedding3 ∘ raw17881step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17881step3 raw17881step3Labels raw17881step4Labels labelEmbedding3 hl
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw17882 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, -1, 1], ![0, -2, 2]]
def raw17882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17882step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17882step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17882step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17882step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17882 raw17882Labels = mixedMoment B node5413 node5413Labels := by
  calc
    mixedMoment B raw17882 raw17882Labels = mixedMoment B raw17882step0 raw17882step0Labels := by
      have hz : ∀ j, raw17882 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17882step0 = (fun i j => raw17882 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17882step0 raw17882; decide +kernel
      have hl : raw17882step0Labels = raw17882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17882 raw17882Labels permutation434 hz
    mixedMoment B raw17882step0 raw17882step0Labels = mixedMoment B raw17882step1 raw17882step1Labels := by
      have hz : ∀ j, raw17882step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17882step1 = (fun i j => raw17882step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17882step1 raw17882step0; decide +kernel
      have hl : raw17882step1Labels = raw17882step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17882step0 raw17882step0Labels permutation80 hz
    mixedMoment B raw17882step1 raw17882step1Labels = mixedMoment B raw17882step2 raw17882step2Labels := by
      have ha : raw17882step2 = (fun i j => raw17882step1 (permutation30 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17882step2 raw17882step1; decide +kernel
      have hl : raw17882step2Labels = raw17882step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17882step1 raw17882step1Labels permutation30 permutation4
    mixedMoment B raw17882step2 raw17882step2Labels = mixedMoment B raw17882step3 raw17882step3Labels := by
      have ha : raw17882step3 = raw17882step2 := by apply Matrix.ext; unfold raw17882step3 raw17882step2; decide +kernel
      have hl : raw17882step2Labels = labelEmbedding7 ∘ raw17882step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17882step2 raw17882step2Labels raw17882step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5413 node5413Labels := by rfl

def raw17883 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17883step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17883step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17883step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17883step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17883 raw17883Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw17883 raw17883Labels = mixedMoment B raw17883step0 raw17883step0Labels := by
      have hz : ∀ j, raw17883 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17883step0 = (fun i j => raw17883 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17883step0 raw17883; decide +kernel
      have hl : raw17883step0Labels = raw17883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17883 raw17883Labels permutation434 hz
    mixedMoment B raw17883step0 raw17883step0Labels = mixedMoment B raw17883step1 raw17883step1Labels := by
      have ha : raw17883step1 = (fun i j => raw17883step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17883step1 raw17883step0; decide +kernel
      have hl : raw17883step1Labels = raw17883step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17883step0 raw17883step0Labels permutation151 permutation6
    mixedMoment B raw17883step1 raw17883step1Labels = mixedMoment B raw17883step2 raw17883step2Labels := by
      have ha : raw17883step2 = -raw17883step1 := by apply Matrix.ext; change ∀ i j, raw17883step2 i j = -(raw17883step1 i j); unfold raw17883step2 raw17883step1; decide +kernel
      have hl : raw17883step2Labels = raw17883step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17883step2 raw17883step2Labels = mixedMoment B raw17883step3 raw17883step3Labels := by
      have ha : raw17883step3 = raw17883step2 := by apply Matrix.ext; unfold raw17883step3 raw17883step2; decide +kernel
      have hl : raw17883step2Labels = labelEmbedding9 ∘ raw17883step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17883step2 raw17883step2Labels raw17883step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw17884 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw17884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw17884step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17884step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17884step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17884 raw17884Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw17884 raw17884Labels = mixedMoment B raw17884step0 raw17884step0Labels := by
      have hz : ∀ j, raw17884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17884step0 = (fun i j => raw17884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17884step0 raw17884; decide +kernel
      have hl : raw17884step0Labels = raw17884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17884 raw17884Labels permutation346 hz
    mixedMoment B raw17884step0 raw17884step0Labels = mixedMoment B raw17884step1 raw17884step1Labels := by
      have ha : raw17884step1 = (fun i j => raw17884step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17884step1 raw17884step0; decide +kernel
      have hl : raw17884step1Labels = raw17884step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17884step0 raw17884step0Labels permutation151 permutation4
    mixedMoment B raw17884step1 raw17884step1Labels = mixedMoment B raw17884step2 raw17884step2Labels := by
      have ha : raw17884step2 = raw17884step1 := by apply Matrix.ext; unfold raw17884step2 raw17884step1; decide +kernel
      have hl : raw17884step1Labels = labelEmbedding7 ∘ raw17884step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17884step1 raw17884step1Labels raw17884step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5101 node5101Labels := by rfl

def raw17885 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw17885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw17885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17885step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17885step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17885step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17885step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17885 raw17885Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw17885 raw17885Labels = mixedMoment B raw17885step0 raw17885step0Labels := by
      have hz : ∀ j, raw17885 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17885step0 = (fun i j => raw17885 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17885step0 raw17885; decide +kernel
      have hl : raw17885step0Labels = raw17885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17885 raw17885Labels permutation346 hz
    mixedMoment B raw17885step0 raw17885step0Labels = mixedMoment B raw17885step1 raw17885step1Labels := by
      have ha : raw17885step1 = (fun i j => raw17885step0 (permutation150 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17885step1 raw17885step0; decide +kernel
      have hl : raw17885step1Labels = raw17885step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17885step0 raw17885step0Labels permutation150 permutation4
    mixedMoment B raw17885step1 raw17885step1Labels = mixedMoment B raw17885step2 raw17885step2Labels := by
      have ha : raw17885step2 = raw17885step1 := by apply Matrix.ext; unfold raw17885step2 raw17885step1; decide +kernel
      have hl : raw17885step1Labels = labelEmbedding7 ∘ raw17885step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17885step1 raw17885step1Labels raw17885step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw17886 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2]]
def raw17886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17886step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17886step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17886 raw17886Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw17886 raw17886Labels = mixedMoment B raw17886step0 raw17886step0Labels := by
      have ha : raw17886step0 = (fun i j => raw17886 (permutation682 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17886step0 raw17886; decide +kernel
      have hl : raw17886step0Labels = raw17886Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17886 raw17886Labels permutation682 permutation4
    mixedMoment B raw17886step0 raw17886step0Labels = mixedMoment B raw17886step1 raw17886step1Labels := by
      have ha : raw17886step1 = raw17886step0 := by apply Matrix.ext; unfold raw17886step1 raw17886step0; decide +kernel
      have hl : raw17886step0Labels = labelEmbedding7 ∘ raw17886step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17886step0 raw17886step0Labels raw17886step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5098 node5098Labels := by rfl

def raw17887 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -3, 2]]
def raw17887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 2, 0], ![0, -1, 1], ![1, -3, 2]]
def raw17887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17887step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17887step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17887 raw17887Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw17887 raw17887Labels = mixedMoment B raw17887step0 raw17887step0Labels := by
      have hz : ∀ j, raw17887 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17887step0 = (fun i j => raw17887 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17887step0 raw17887; decide +kernel
      have hl : raw17887step0Labels = raw17887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17887 raw17887Labels permutation346 hz
    mixedMoment B raw17887step0 raw17887step0Labels = mixedMoment B raw17887step1 raw17887step1Labels := by
      have ha : raw17887step1 = (fun i j => raw17887step0 (permutation148 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17887step1 raw17887step0; decide +kernel
      have hl : raw17887step1Labels = raw17887step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17887step0 raw17887step0Labels permutation148 permutation4
    mixedMoment B raw17887step1 raw17887step1Labels = mixedMoment B raw17887step2 raw17887step2Labels := by
      have ha : raw17887step2 = raw17887step1 := by apply Matrix.ext; unfold raw17887step2 raw17887step1; decide +kernel
      have hl : raw17887step1Labels = labelEmbedding7 ∘ raw17887step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17887step1 raw17887step1Labels raw17887step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw17888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17888step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17888 raw17888Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw17888 raw17888Labels = mixedMoment B raw17888step0 raw17888step0Labels := by
      have hz : ∀ j, raw17888 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17888step0 = (fun i j => raw17888 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17888step0 raw17888; decide +kernel
      have hl : raw17888step0Labels = raw17888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17888 raw17888Labels permutation434 hz
    mixedMoment B raw17888step0 raw17888step0Labels = mixedMoment B raw17888step1 raw17888step1Labels := by
      have ha : raw17888step1 = (fun i j => raw17888step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17888step1 raw17888step0; decide +kernel
      have hl : raw17888step1Labels = raw17888step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17888step0 raw17888step0Labels permutation56 permutation2
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw17889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw17889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17889step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17889step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17889 raw17889Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw17889 raw17889Labels = mixedMoment B raw17889step0 raw17889step0Labels := by
      have hz : ∀ j, raw17889 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17889step0 = (fun i j => raw17889 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17889step0 raw17889; decide +kernel
      have hl : raw17889step0Labels = raw17889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17889 raw17889Labels permutation434 hz
    mixedMoment B raw17889step0 raw17889step0Labels = mixedMoment B raw17889step1 raw17889step1Labels := by
      have ha : raw17889step1 = (fun i j => raw17889step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17889step1 raw17889step0; decide +kernel
      have hl : raw17889step1Labels = raw17889step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17889step0 raw17889step0Labels permutation150 permutation2
    mixedMoment B raw17889step1 raw17889step1Labels = mixedMoment B raw17889step2 raw17889step2Labels := by
      have ha : raw17889step2 = -raw17889step1 := by apply Matrix.ext; change ∀ i j, raw17889step2 i j = -(raw17889step1 i j); unfold raw17889step2 raw17889step1; decide +kernel
      have hl : raw17889step2Labels = raw17889step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw17890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17890step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17890 raw17890Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17890 raw17890Labels = mixedMoment B raw17890step0 raw17890step0Labels := by
      have ha : raw17890step0 = (fun i j => raw17890 (permutation645 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17890step0 raw17890; decide +kernel
      have hl : raw17890step0Labels = raw17890Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17890 raw17890Labels permutation645 permutation7
    mixedMoment B raw17890step0 raw17890step0Labels = mixedMoment B raw17890step1 raw17890step1Labels := by
      have ha : raw17890step1 = raw17890step0 := by apply Matrix.ext; unfold raw17890step1 raw17890step0; decide +kernel
      have hl : raw17890step0Labels = labelEmbedding10 ∘ raw17890step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17890step0 raw17890step0Labels raw17890step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw17891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw17891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17891step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![2, 0, -2]]
def raw17891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17891step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17891step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17891step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17891step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17891 raw17891Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw17891 raw17891Labels = mixedMoment B raw17891step0 raw17891step0Labels := by
      have hz : ∀ j, raw17891 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17891step0 = (fun i j => raw17891 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17891step0 raw17891; decide +kernel
      have hl : raw17891step0Labels = raw17891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17891 raw17891Labels permutation520 hz
    mixedMoment B raw17891step0 raw17891step0Labels = mixedMoment B raw17891step1 raw17891step1Labels := by
      have hz : ∀ j, raw17891step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw17891step1 = (fun i j => raw17891step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw17891step1 raw17891step0; decide +kernel
      have hl : raw17891step1Labels = raw17891step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17891step0 raw17891step0Labels permutation104 hz
    mixedMoment B raw17891step1 raw17891step1Labels = mixedMoment B raw17891step2 raw17891step2Labels := by
      have ha : raw17891step2 = (fun i j => raw17891step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17891step2 raw17891step1; decide +kernel
      have hl : raw17891step2Labels = raw17891step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17891step1 raw17891step1Labels permutation30 permutation7
    mixedMoment B raw17891step2 raw17891step2Labels = mixedMoment B raw17891step3 raw17891step3Labels := by
      have ha : raw17891step3 = raw17891step2 := by apply Matrix.ext; unfold raw17891step3 raw17891step2; decide +kernel
      have hl : raw17891step2Labels = labelEmbedding10 ∘ raw17891step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17891step2 raw17891step2Labels raw17891step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw17892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw17892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17892step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17892step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17892step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17892 raw17892Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw17892 raw17892Labels = mixedMoment B raw17892step0 raw17892step0Labels := by
      have hz : ∀ j, raw17892 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17892step0 = (fun i j => raw17892 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17892step0 raw17892; decide +kernel
      have hl : raw17892step0Labels = raw17892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17892 raw17892Labels permutation434 hz
    mixedMoment B raw17892step0 raw17892step0Labels = mixedMoment B raw17892step1 raw17892step1Labels := by
      have ha : raw17892step1 = (fun i j => raw17892step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17892step1 raw17892step0; decide +kernel
      have hl : raw17892step1Labels = raw17892step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17892step0 raw17892step0Labels permutation144 permutation6
    mixedMoment B raw17892step1 raw17892step1Labels = mixedMoment B raw17892step2 raw17892step2Labels := by
      have ha : raw17892step2 = raw17892step1 := by apply Matrix.ext; unfold raw17892step2 raw17892step1; decide +kernel
      have hl : raw17892step1Labels = labelEmbedding9 ∘ raw17892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17892step1 raw17892step1Labels raw17892step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw17893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17893step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17893step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17893 raw17893Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw17893 raw17893Labels = mixedMoment B raw17893step0 raw17893step0Labels := by
      have hz : ∀ j, raw17893 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17893step0 = (fun i j => raw17893 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17893step0 raw17893; decide +kernel
      have hl : raw17893step0Labels = raw17893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17893 raw17893Labels permutation434 hz
    mixedMoment B raw17893step0 raw17893step0Labels = mixedMoment B raw17893step1 raw17893step1Labels := by
      have ha : raw17893step1 = (fun i j => raw17893step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17893step1 raw17893step0; decide +kernel
      have hl : raw17893step1Labels = raw17893step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17893step0 raw17893step0Labels permutation38 permutation3
    mixedMoment B raw17893step1 raw17893step1Labels = mixedMoment B raw17893step2 raw17893step2Labels := by
      have ha : raw17893step2 = raw17893step1 := by apply Matrix.ext; unfold raw17893step2 raw17893step1; decide +kernel
      have hl : raw17893step1Labels = labelEmbedding6 ∘ raw17893step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17893step1 raw17893step1Labels raw17893step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw17894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw17894step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw17894step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17894 raw17894Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw17894 raw17894Labels = mixedMoment B raw17894step0 raw17894step0Labels := by
      have hz : ∀ j, raw17894 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17894step0 = (fun i j => raw17894 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17894step0 raw17894; decide +kernel
      have hl : raw17894step0Labels = raw17894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17894 raw17894Labels permutation434 hz
    mixedMoment B raw17894step0 raw17894step0Labels = mixedMoment B raw17894step1 raw17894step1Labels := by
      have ha : raw17894step1 = (fun i j => raw17894step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17894step1 raw17894step0; decide +kernel
      have hl : raw17894step1Labels = raw17894step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17894step0 raw17894step0Labels permutation149 permutation2
    mixedMoment B raw17894step1 raw17894step1Labels = mixedMoment B raw17894step2 raw17894step2Labels := by
      have ha : raw17894step2 = -raw17894step1 := by apply Matrix.ext; change ∀ i j, raw17894step2 i j = -(raw17894step1 i j); unfold raw17894step2 raw17894step1; decide +kernel
      have hl : raw17894step2Labels = raw17894step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5436 node5436Labels := by rfl

def raw17895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17895step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17895 raw17895Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw17895 raw17895Labels = mixedMoment B raw17895step0 raw17895step0Labels := by
      have ha : raw17895step0 = (fun i j => raw17895 (permutation645 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17895step0 raw17895; decide +kernel
      have hl : raw17895step0Labels = raw17895Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17895 raw17895Labels permutation645 permutation7
    mixedMoment B raw17895step0 raw17895step0Labels = mixedMoment B raw17895step1 raw17895step1Labels := by
      have ha : raw17895step1 = raw17895step0 := by apply Matrix.ext; unfold raw17895step1 raw17895step0; decide +kernel
      have hl : raw17895step0Labels = labelEmbedding10 ∘ raw17895step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17895step0 raw17895step0Labels raw17895step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw17896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw17896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw17896step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17896step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17896step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17896step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17896step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17896 raw17896Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw17896 raw17896Labels = mixedMoment B raw17896step0 raw17896step0Labels := by
      have hz : ∀ j, raw17896 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17896step0 = (fun i j => raw17896 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17896step0 raw17896; decide +kernel
      have hl : raw17896step0Labels = raw17896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17896 raw17896Labels permutation520 hz
    mixedMoment B raw17896step0 raw17896step0Labels = mixedMoment B raw17896step1 raw17896step1Labels := by
      have hz : ∀ j, raw17896step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw17896step1 = (fun i j => raw17896step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw17896step1 raw17896step0; decide +kernel
      have hl : raw17896step1Labels = raw17896step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17896step0 raw17896step0Labels permutation104 hz
    mixedMoment B raw17896step1 raw17896step1Labels = mixedMoment B raw17896step2 raw17896step2Labels := by
      have ha : raw17896step2 = (fun i j => raw17896step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17896step2 raw17896step1; decide +kernel
      have hl : raw17896step2Labels = raw17896step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17896step1 raw17896step1Labels permutation30 permutation7
    mixedMoment B raw17896step2 raw17896step2Labels = mixedMoment B raw17896step3 raw17896step3Labels := by
      have ha : raw17896step3 = raw17896step2 := by apply Matrix.ext; unfold raw17896step3 raw17896step2; decide +kernel
      have hl : raw17896step2Labels = labelEmbedding10 ∘ raw17896step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17896step2 raw17896step2Labels raw17896step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw17897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw17897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17897step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17897step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17897step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17897 raw17897Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw17897 raw17897Labels = mixedMoment B raw17897step0 raw17897step0Labels := by
      have hz : ∀ j, raw17897 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17897step0 = (fun i j => raw17897 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17897step0 raw17897; decide +kernel
      have hl : raw17897step0Labels = raw17897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17897 raw17897Labels permutation434 hz
    mixedMoment B raw17897step0 raw17897step0Labels = mixedMoment B raw17897step1 raw17897step1Labels := by
      have ha : raw17897step1 = (fun i j => raw17897step0 (permutation68 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17897step1 raw17897step0; decide +kernel
      have hl : raw17897step1Labels = raw17897step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17897step0 raw17897step0Labels permutation68 permutation4
    mixedMoment B raw17897step1 raw17897step1Labels = mixedMoment B raw17897step2 raw17897step2Labels := by
      have ha : raw17897step2 = raw17897step1 := by apply Matrix.ext; unfold raw17897step2 raw17897step1; decide +kernel
      have hl : raw17897step1Labels = labelEmbedding7 ∘ raw17897step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17897step1 raw17897step1Labels raw17897step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw17898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17898step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17898step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17898step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17898 raw17898Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw17898 raw17898Labels = mixedMoment B raw17898step0 raw17898step0Labels := by
      have hz : ∀ j, raw17898 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17898step0 = (fun i j => raw17898 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17898step0 raw17898; decide +kernel
      have hl : raw17898step0Labels = raw17898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17898 raw17898Labels permutation434 hz
    mixedMoment B raw17898step0 raw17898step0Labels = mixedMoment B raw17898step1 raw17898step1Labels := by
      have ha : raw17898step1 = (fun i j => raw17898step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17898step1 raw17898step0; decide +kernel
      have hl : raw17898step1Labels = raw17898step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17898step0 raw17898step0Labels permutation32 permutation3
    mixedMoment B raw17898step1 raw17898step1Labels = mixedMoment B raw17898step2 raw17898step2Labels := by
      have ha : raw17898step2 = raw17898step1 := by apply Matrix.ext; unfold raw17898step2 raw17898step1; decide +kernel
      have hl : raw17898step1Labels = labelEmbedding6 ∘ raw17898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17898step1 raw17898step1Labels raw17898step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw17899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17899step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17899 raw17899Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw17899 raw17899Labels = mixedMoment B raw17899step0 raw17899step0Labels := by
      have hz : ∀ j, raw17899 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17899step0 = (fun i j => raw17899 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17899step0 raw17899; decide +kernel
      have hl : raw17899step0Labels = raw17899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17899 raw17899Labels permutation434 hz
    mixedMoment B raw17899step0 raw17899step0Labels = mixedMoment B raw17899step1 raw17899step1Labels := by
      have ha : raw17899step1 = (fun i j => raw17899step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17899step1 raw17899step0; decide +kernel
      have hl : raw17899step1Labels = raw17899step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17899step0 raw17899step0Labels permutation58 permutation2
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw17900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17900step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17900step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17900 raw17900Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw17900 raw17900Labels = mixedMoment B raw17900step0 raw17900step0Labels := by
      have ha : raw17900step0 = (fun i j => raw17900 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17900step0 raw17900; decide +kernel
      have hl : raw17900step0Labels = raw17900Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17900 raw17900Labels permutation646 permutation2
    mixedMoment B raw17900step0 raw17900step0Labels = mixedMoment B raw17900step1 raw17900step1Labels := by
      have ha : raw17900step1 = -raw17900step0 := by apply Matrix.ext; change ∀ i j, raw17900step1 i j = -(raw17900step0 i j); unfold raw17900step1 raw17900step0; decide +kernel
      have hl : raw17900step1Labels = raw17900step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw17901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw17901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw17901step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17901step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17901step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17901step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17901step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17901 raw17901Labels = mixedMoment B node5413 node5413Labels := by
  calc
    mixedMoment B raw17901 raw17901Labels = mixedMoment B raw17901step0 raw17901step0Labels := by
      have hz : ∀ j, raw17901 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17901step0 = (fun i j => raw17901 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17901step0 raw17901; decide +kernel
      have hl : raw17901step0Labels = raw17901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17901 raw17901Labels permutation520 hz
    mixedMoment B raw17901step0 raw17901step0Labels = mixedMoment B raw17901step1 raw17901step1Labels := by
      have hz : ∀ j, raw17901step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw17901step1 = (fun i j => raw17901step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw17901step1 raw17901step0; decide +kernel
      have hl : raw17901step1Labels = raw17901step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17901step0 raw17901step0Labels permutation104 hz
    mixedMoment B raw17901step1 raw17901step1Labels = mixedMoment B raw17901step2 raw17901step2Labels := by
      have ha : raw17901step2 = (fun i j => raw17901step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17901step2 raw17901step1; decide +kernel
      have hl : raw17901step2Labels = raw17901step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17901step1 raw17901step1Labels permutation31 permutation2
    mixedMoment B raw17901step2 raw17901step2Labels = mixedMoment B raw17901step3 raw17901step3Labels := by
      have ha : raw17901step3 = -raw17901step2 := by apply Matrix.ext; change ∀ i j, raw17901step3 i j = -(raw17901step2 i j); unfold raw17901step3 raw17901step2; decide +kernel
      have hl : raw17901step3Labels = raw17901step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5413 node5413Labels := by rfl

def raw17902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw17902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17902step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17902step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17902step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17902step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17902step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17902 raw17902Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw17902 raw17902Labels = mixedMoment B raw17902step0 raw17902step0Labels := by
      have hz : ∀ j, raw17902 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17902step0 = (fun i j => raw17902 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17902step0 raw17902; decide +kernel
      have hl : raw17902step0Labels = raw17902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17902 raw17902Labels permutation434 hz
    mixedMoment B raw17902step0 raw17902step0Labels = mixedMoment B raw17902step1 raw17902step1Labels := by
      have ha : raw17902step1 = (fun i j => raw17902step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17902step1 raw17902step0; decide +kernel
      have hl : raw17902step1Labels = raw17902step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17902step0 raw17902step0Labels permutation58 permutation7
    mixedMoment B raw17902step1 raw17902step1Labels = mixedMoment B raw17902step2 raw17902step2Labels := by
      have ha : raw17902step2 = -raw17902step1 := by apply Matrix.ext; change ∀ i j, raw17902step2 i j = -(raw17902step1 i j); unfold raw17902step2 raw17902step1; decide +kernel
      have hl : raw17902step2Labels = raw17902step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17902step2 raw17902step2Labels = mixedMoment B raw17902step3 raw17902step3Labels := by
      have ha : raw17902step3 = raw17902step2 := by apply Matrix.ext; unfold raw17902step3 raw17902step2; decide +kernel
      have hl : raw17902step2Labels = labelEmbedding10 ∘ raw17902step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17902step2 raw17902step2Labels raw17902step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw17903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17903step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17903step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17903 raw17903Labels = mixedMoment B node5187 node5187Labels := by
  calc
    mixedMoment B raw17903 raw17903Labels = mixedMoment B raw17903step0 raw17903step0Labels := by
      have ha : raw17903step0 = (fun i j => raw17903 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17903step0 raw17903; decide +kernel
      have hl : raw17903step0Labels = raw17903Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17903 raw17903Labels permutation152 permutation3
    mixedMoment B raw17903step0 raw17903step0Labels = mixedMoment B raw17903step1 raw17903step1Labels := by
      have ha : raw17903step1 = raw17903step0 := by apply Matrix.ext; unfold raw17903step1 raw17903step0; decide +kernel
      have hl : raw17903step0Labels = labelEmbedding6 ∘ raw17903step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17903step0 raw17903step0Labels raw17903step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5187 node5187Labels := by rfl

def raw17904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17904step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17904 raw17904Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw17904 raw17904Labels = mixedMoment B raw17904step0 raw17904step0Labels := by
      have ha : raw17904step0 = (fun i j => raw17904 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17904step0 raw17904; decide +kernel
      have hl : raw17904step0Labels = raw17904Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17904 raw17904Labels permutation265 permutation2
    _ = mixedMoment B node5351 node5351Labels := by rfl

def raw17905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17905step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17905 raw17905Labels = mixedMoment B node5414 node5414Labels := by
  calc
    mixedMoment B raw17905 raw17905Labels = mixedMoment B raw17905step0 raw17905step0Labels := by
      have ha : raw17905step0 = (fun i j => raw17905 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17905step0 raw17905; decide +kernel
      have hl : raw17905step0Labels = raw17905Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17905 raw17905Labels permutation664 permutation2
    mixedMoment B raw17905step0 raw17905step0Labels = mixedMoment B raw17905step1 raw17905step1Labels := by
      have ha : raw17905step1 = -raw17905step0 := by apply Matrix.ext; change ∀ i j, raw17905step1 i j = -(raw17905step0 i j); unfold raw17905step1 raw17905step0; decide +kernel
      have hl : raw17905step1Labels = raw17905step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5414 node5414Labels := by rfl

def raw17906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw17906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17906step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17906step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17906step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17906 raw17906Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw17906 raw17906Labels = mixedMoment B raw17906step0 raw17906step0Labels := by
      have hz : ∀ j, raw17906 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17906step0 = (fun i j => raw17906 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17906step0 raw17906; decide +kernel
      have hl : raw17906step0Labels = raw17906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17906 raw17906Labels permutation520 hz
    mixedMoment B raw17906step0 raw17906step0Labels = mixedMoment B raw17906step1 raw17906step1Labels := by
      have ha : raw17906step1 = (fun i j => raw17906step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17906step1 raw17906step0; decide +kernel
      have hl : raw17906step1Labels = raw17906step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17906step0 raw17906step0Labels permutation151 permutation2
    mixedMoment B raw17906step1 raw17906step1Labels = mixedMoment B raw17906step2 raw17906step2Labels := by
      have ha : raw17906step2 = -raw17906step1 := by apply Matrix.ext; change ∀ i j, raw17906step2 i j = -(raw17906step1 i j); unfold raw17906step2 raw17906step1; decide +kernel
      have hl : raw17906step2Labels = raw17906step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw17907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17907step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17907step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17907step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17907step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17907step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17907 raw17907Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw17907 raw17907Labels = mixedMoment B raw17907step0 raw17907step0Labels := by
      have ha : raw17907step0 = (fun i j => raw17907 (permutation273 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17907step0 raw17907; decide +kernel
      have hl : raw17907step0Labels = raw17907Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17907 raw17907Labels permutation273 permutation7
    mixedMoment B raw17907step0 raw17907step0Labels = mixedMoment B raw17907step1 raw17907step1Labels := by
      have ha : raw17907step1 = -raw17907step0 := by apply Matrix.ext; change ∀ i j, raw17907step1 i j = -(raw17907step0 i j); unfold raw17907step1 raw17907step0; decide +kernel
      have hl : raw17907step1Labels = raw17907step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17907step1 raw17907step1Labels = mixedMoment B raw17907step2 raw17907step2Labels := by
      have ha : raw17907step2 = raw17907step1 := by apply Matrix.ext; unfold raw17907step2 raw17907step1; decide +kernel
      have hl : raw17907step1Labels = labelEmbedding10 ∘ raw17907step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17907step1 raw17907step1Labels raw17907step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5471 node5471Labels := by rfl

def raw17908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17908step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17908step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17908step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17908step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17908 raw17908Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw17908 raw17908Labels = mixedMoment B raw17908step0 raw17908step0Labels := by
      have hz : ∀ j, raw17908 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17908step0 = (fun i j => raw17908 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17908step0 raw17908; decide +kernel
      have hl : raw17908step0Labels = raw17908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17908 raw17908Labels permutation434 hz
    mixedMoment B raw17908step0 raw17908step0Labels = mixedMoment B raw17908step1 raw17908step1Labels := by
      have ha : raw17908step1 = (fun i j => raw17908step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17908step1 raw17908step0; decide +kernel
      have hl : raw17908step1Labels = raw17908step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17908step0 raw17908step0Labels permutation33 permutation3
    mixedMoment B raw17908step1 raw17908step1Labels = mixedMoment B raw17908step2 raw17908step2Labels := by
      have ha : raw17908step2 = raw17908step1 := by apply Matrix.ext; unfold raw17908step2 raw17908step1; decide +kernel
      have hl : raw17908step1Labels = labelEmbedding6 ∘ raw17908step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17908step1 raw17908step1Labels raw17908step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5188 node5188Labels := by rfl

def raw17909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17909step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17909 raw17909Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw17909 raw17909Labels = mixedMoment B raw17909step0 raw17909step0Labels := by
      have hz : ∀ j, raw17909 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17909step0 = (fun i j => raw17909 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17909step0 raw17909; decide +kernel
      have hl : raw17909step0Labels = raw17909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17909 raw17909Labels permutation434 hz
    mixedMoment B raw17909step0 raw17909step0Labels = mixedMoment B raw17909step1 raw17909step1Labels := by
      have ha : raw17909step1 = (fun i j => raw17909step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17909step1 raw17909step0; decide +kernel
      have hl : raw17909step1Labels = raw17909step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17909step0 raw17909step0Labels permutation56 permutation2
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw17910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17910Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17910step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17910step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17910step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17910step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17910 raw17910Labels = mixedMoment B node5385 node5385Labels := by
  calc
    mixedMoment B raw17910 raw17910Labels = mixedMoment B raw17910step0 raw17910step0Labels := by
      have hz : ∀ j, raw17910 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17910step0 = (fun i j => raw17910 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17910step0 raw17910; decide +kernel
      have hl : raw17910step0Labels = raw17910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17910 raw17910Labels permutation434 hz
    mixedMoment B raw17910step0 raw17910step0Labels = mixedMoment B raw17910step1 raw17910step1Labels := by
      have ha : raw17910step1 = (fun i j => raw17910step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17910step1 raw17910step0; decide +kernel
      have hl : raw17910step1Labels = raw17910step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17910step0 raw17910step0Labels permutation151 permutation2
    mixedMoment B raw17910step1 raw17910step1Labels = mixedMoment B raw17910step2 raw17910step2Labels := by
      have ha : raw17910step2 = -raw17910step1 := by apply Matrix.ext; change ∀ i j, raw17910step2 i j = -(raw17910step1 i j); unfold raw17910step2 raw17910step1; decide +kernel
      have hl : raw17910step2Labels = raw17910step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5385 node5385Labels := by rfl

def raw17911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw17911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17911step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17911step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17911step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17911 raw17911Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw17911 raw17911Labels = mixedMoment B raw17911step0 raw17911step0Labels := by
      have ha : raw17911step0 = (fun i j => raw17911 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17911step0 raw17911; decide +kernel
      have hl : raw17911step0Labels = raw17911Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17911 raw17911Labels permutation682 permutation2
    mixedMoment B raw17911step0 raw17911step0Labels = mixedMoment B raw17911step1 raw17911step1Labels := by
      have ha : raw17911step1 = -raw17911step0 := by apply Matrix.ext; change ∀ i j, raw17911step1 i j = -(raw17911step0 i j); unfold raw17911step1 raw17911step0; decide +kernel
      have hl : raw17911step1Labels = raw17911step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw17912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw17912Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 1, -2]]
def raw17912step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17912step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17912step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17912step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17912step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17912step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17912step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17912 raw17912Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw17912 raw17912Labels = mixedMoment B raw17912step0 raw17912step0Labels := by
      have hz : ∀ j, raw17912 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17912step0 = (fun i j => raw17912 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17912step0 raw17912; decide +kernel
      have hl : raw17912step0Labels = raw17912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17912 raw17912Labels permutation434 hz
    mixedMoment B raw17912step0 raw17912step0Labels = mixedMoment B raw17912step1 raw17912step1Labels := by
      have ha : raw17912step1 = (fun i j => raw17912step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17912step1 raw17912step0; decide +kernel
      have hl : raw17912step1Labels = raw17912step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17912step0 raw17912step0Labels permutation127 permutation3
    mixedMoment B raw17912step1 raw17912step1Labels = mixedMoment B raw17912step2 raw17912step2Labels := by
      have ha : raw17912step2 = -raw17912step1 := by apply Matrix.ext; change ∀ i j, raw17912step2 i j = -(raw17912step1 i j); unfold raw17912step2 raw17912step1; decide +kernel
      have hl : raw17912step2Labels = raw17912step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17912step2 raw17912step2Labels = mixedMoment B raw17912step3 raw17912step3Labels := by
      have ha : raw17912step3 = raw17912step2 := by apply Matrix.ext; unfold raw17912step3 raw17912step2; decide +kernel
      have hl : raw17912step2Labels = labelEmbedding6 ∘ raw17912step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17912step2 raw17912step2Labels raw17912step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw17913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw17913step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw17913step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17913step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw17913step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17913 raw17913Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw17913 raw17913Labels = mixedMoment B raw17913step0 raw17913step0Labels := by
      have hz : ∀ j, raw17913 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17913step0 = (fun i j => raw17913 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17913step0 raw17913; decide +kernel
      have hl : raw17913step0Labels = raw17913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17913 raw17913Labels permutation434 hz
    mixedMoment B raw17913step0 raw17913step0Labels = mixedMoment B raw17913step1 raw17913step1Labels := by
      have ha : raw17913step1 = (fun i j => raw17913step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17913step1 raw17913step0; decide +kernel
      have hl : raw17913step1Labels = raw17913step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17913step0 raw17913step0Labels permutation151 permutation2
    mixedMoment B raw17913step1 raw17913step1Labels = mixedMoment B raw17913step2 raw17913step2Labels := by
      have ha : raw17913step2 = -raw17913step1 := by apply Matrix.ext; change ∀ i j, raw17913step2 i j = -(raw17913step1 i j); unfold raw17913step2 raw17913step1; decide +kernel
      have hl : raw17913step2Labels = raw17913step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5139 node5139Labels := by rfl

def raw17914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw17914step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17914step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17914step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17914step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17914 raw17914Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw17914 raw17914Labels = mixedMoment B raw17914step0 raw17914step0Labels := by
      have hz : ∀ j, raw17914 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17914step0 = (fun i j => raw17914 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17914step0 raw17914; decide +kernel
      have hl : raw17914step0Labels = raw17914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17914 raw17914Labels permutation434 hz
    mixedMoment B raw17914step0 raw17914step0Labels = mixedMoment B raw17914step1 raw17914step1Labels := by
      have ha : raw17914step1 = (fun i j => raw17914step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17914step1 raw17914step0; decide +kernel
      have hl : raw17914step1Labels = raw17914step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17914step0 raw17914step0Labels permutation150 permutation2
    mixedMoment B raw17914step1 raw17914step1Labels = mixedMoment B raw17914step2 raw17914step2Labels := by
      have ha : raw17914step2 = -raw17914step1 := by apply Matrix.ext; change ∀ i j, raw17914step2 i j = -(raw17914step1 i j); unfold raw17914step2 raw17914step1; decide +kernel
      have hl : raw17914step2Labels = raw17914step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw17915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17915Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -1, -2]]
def raw17915step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17915step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17915step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17915step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17915 raw17915Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw17915 raw17915Labels = mixedMoment B raw17915step0 raw17915step0Labels := by
      have hz : ∀ j, raw17915 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17915step0 = (fun i j => raw17915 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17915step0 raw17915; decide +kernel
      have hl : raw17915step0Labels = raw17915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17915 raw17915Labels permutation434 hz
    mixedMoment B raw17915step0 raw17915step0Labels = mixedMoment B raw17915step1 raw17915step1Labels := by
      have ha : raw17915step1 = (fun i j => raw17915step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17915step1 raw17915step0; decide +kernel
      have hl : raw17915step1Labels = raw17915step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17915step0 raw17915step0Labels permutation151 permutation2
    mixedMoment B raw17915step1 raw17915step1Labels = mixedMoment B raw17915step2 raw17915step2Labels := by
      have ha : raw17915step2 = -raw17915step1 := by apply Matrix.ext; change ∀ i j, raw17915step2 i j = -(raw17915step1 i j); unfold raw17915step2 raw17915step1; decide +kernel
      have hl : raw17915step2Labels = raw17915step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5164 node5164Labels := by rfl

def raw17916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw17916Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17916step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17916step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17916step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17916 raw17916Labels = mixedMoment B node5135 node5135Labels := by
  calc
    mixedMoment B raw17916 raw17916Labels = mixedMoment B raw17916step0 raw17916step0Labels := by
      have ha : raw17916step0 = (fun i j => raw17916 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17916step0 raw17916; decide +kernel
      have hl : raw17916step0Labels = raw17916Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17916 raw17916Labels permutation682 permutation2
    mixedMoment B raw17916step0 raw17916step0Labels = mixedMoment B raw17916step1 raw17916step1Labels := by
      have ha : raw17916step1 = -raw17916step0 := by apply Matrix.ext; change ∀ i j, raw17916step1 i j = -(raw17916step0 i j); unfold raw17916step1 raw17916step0; decide +kernel
      have hl : raw17916step1Labels = raw17916step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5135 node5135Labels := by rfl

def raw17917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw17917Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2]]
def raw17917step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![3, -1, -2]]
def raw17917step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17917step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17917step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17917step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17917step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17917 raw17917Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw17917 raw17917Labels = mixedMoment B raw17917step0 raw17917step0Labels := by
      have hz : ∀ j, raw17917 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17917step0 = (fun i j => raw17917 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17917step0 raw17917; decide +kernel
      have hl : raw17917step0Labels = raw17917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17917 raw17917Labels permutation520 hz
    mixedMoment B raw17917step0 raw17917step0Labels = mixedMoment B raw17917step1 raw17917step1Labels := by
      have hz : ∀ j, raw17917step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw17917step1 = (fun i j => raw17917step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw17917step1 raw17917step0; decide +kernel
      have hl : raw17917step1Labels = raw17917step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17917step0 raw17917step0Labels permutation104 hz
    mixedMoment B raw17917step1 raw17917step1Labels = mixedMoment B raw17917step2 raw17917step2Labels := by
      have ha : raw17917step2 = (fun i j => raw17917step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17917step2 raw17917step1; decide +kernel
      have hl : raw17917step2Labels = raw17917step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17917step1 raw17917step1Labels permutation31 permutation2
    mixedMoment B raw17917step2 raw17917step2Labels = mixedMoment B raw17917step3 raw17917step3Labels := by
      have ha : raw17917step3 = -raw17917step2 := by apply Matrix.ext; change ∀ i j, raw17917step3 i j = -(raw17917step2 i j); unfold raw17917step3 raw17917step2; decide +kernel
      have hl : raw17917step3Labels = raw17917step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw17918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17918Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17918step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17918step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17918step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17918step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17918step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17918step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17918 raw17918Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw17918 raw17918Labels = mixedMoment B raw17918step0 raw17918step0Labels := by
      have hz : ∀ j, raw17918 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17918step0 = (fun i j => raw17918 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17918step0 raw17918; decide +kernel
      have hl : raw17918step0Labels = raw17918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17918 raw17918Labels permutation434 hz
    mixedMoment B raw17918step0 raw17918step0Labels = mixedMoment B raw17918step1 raw17918step1Labels := by
      have ha : raw17918step1 = (fun i j => raw17918step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17918step1 raw17918step0; decide +kernel
      have hl : raw17918step1Labels = raw17918step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17918step0 raw17918step0Labels permutation58 permutation7
    mixedMoment B raw17918step1 raw17918step1Labels = mixedMoment B raw17918step2 raw17918step2Labels := by
      have ha : raw17918step2 = -raw17918step1 := by apply Matrix.ext; change ∀ i j, raw17918step2 i j = -(raw17918step1 i j); unfold raw17918step2 raw17918step1; decide +kernel
      have hl : raw17918step2Labels = raw17918step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17918step2 raw17918step2Labels = mixedMoment B raw17918step3 raw17918step3Labels := by
      have ha : raw17918step3 = raw17918step2 := by apply Matrix.ext; unfold raw17918step3 raw17918step2; decide +kernel
      have hl : raw17918step2Labels = labelEmbedding1 ∘ raw17918step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17918step2 raw17918step2Labels raw17918step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

def raw17919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17919Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17919step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17919step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17919step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17919 raw17919Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw17919 raw17919Labels = mixedMoment B raw17919step0 raw17919step0Labels := by
      have hz : ∀ j, raw17919 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17919step0 = (fun i j => raw17919 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17919step0 raw17919; decide +kernel
      have hl : raw17919step0Labels = raw17919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17919 raw17919Labels permutation434 hz
    mixedMoment B raw17919step0 raw17919step0Labels = mixedMoment B raw17919step1 raw17919step1Labels := by
      have ha : raw17919step1 = (fun i j => raw17919step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17919step1 raw17919step0; decide +kernel
      have hl : raw17919step1Labels = raw17919step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17919step0 raw17919step0Labels permutation144 permutation7
    mixedMoment B raw17919step1 raw17919step1Labels = mixedMoment B raw17919step2 raw17919step2Labels := by
      have ha : raw17919step2 = raw17919step1 := by apply Matrix.ext; unfold raw17919step2 raw17919step1; decide +kernel
      have hl : raw17919step1Labels = labelEmbedding1 ∘ raw17919step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17919step1 raw17919step1Labels raw17919step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
