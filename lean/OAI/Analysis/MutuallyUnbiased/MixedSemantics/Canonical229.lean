import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw29312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw29312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw29312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29312step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw29312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29312 raw29312Labels = mixedMoment B node2816 node2816Labels := by
  calc
    mixedMoment B raw29312 raw29312Labels = mixedMoment B raw29312step0 raw29312step0Labels := by
      have hz : ∀ j, raw29312 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29312step0 = (fun i j => raw29312 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29312step0 raw29312; decide +kernel
      have hl : raw29312step0Labels = raw29312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29312 raw29312Labels permutation346 hz
    mixedMoment B raw29312step0 raw29312step0Labels = mixedMoment B raw29312step1 raw29312step1Labels := by
      have ha : raw29312step1 = (fun i j => raw29312step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29312step1 raw29312step0; decide +kernel
      have hl : raw29312step1Labels = raw29312step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29312step0 raw29312step0Labels permutation149 permutation2
    mixedMoment B raw29312step1 raw29312step1Labels = mixedMoment B raw29312step2 raw29312step2Labels := by
      have ha : raw29312step2 = -raw29312step1 := by apply Matrix.ext; change ∀ i j, raw29312step2 i j = -(raw29312step1 i j); unfold raw29312step2 raw29312step1; decide +kernel
      have hl : raw29312step2Labels = raw29312step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2816 node2816Labels := by rfl

def raw29313 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29313Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29313step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw29313step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw29313step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29313 raw29313Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw29313 raw29313Labels = mixedMoment B raw29313step0 raw29313step0Labels := by
      have hz : ∀ j, raw29313 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29313step0 = (fun i j => raw29313 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29313step0 raw29313; decide +kernel
      have hl : raw29313step0Labels = raw29313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29313 raw29313Labels permutation346 hz
    mixedMoment B raw29313step0 raw29313step0Labels = mixedMoment B raw29313step1 raw29313step1Labels := by
      have ha : raw29313step1 = (fun i j => raw29313step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29313step1 raw29313step0; decide +kernel
      have hl : raw29313step1Labels = raw29313step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29313step0 raw29313step0Labels permutation34 permutation4
    mixedMoment B raw29313step1 raw29313step1Labels = mixedMoment B raw29313step2 raw29313step2Labels := by
      have ha : raw29313step2 = -raw29313step1 := by apply Matrix.ext; change ∀ i j, raw29313step2 i j = -(raw29313step1 i j); unfold raw29313step2 raw29313step1; decide +kernel
      have hl : raw29313step2Labels = raw29313step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3612 node3612Labels := by rfl

def raw29314 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29314Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29314step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw29314step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw29314step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29314 raw29314Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw29314 raw29314Labels = mixedMoment B raw29314step0 raw29314step0Labels := by
      have hz : ∀ j, raw29314 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29314step0 = (fun i j => raw29314 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29314step0 raw29314; decide +kernel
      have hl : raw29314step0Labels = raw29314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29314 raw29314Labels permutation346 hz
    mixedMoment B raw29314step0 raw29314step0Labels = mixedMoment B raw29314step1 raw29314step1Labels := by
      have ha : raw29314step1 = (fun i j => raw29314step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29314step1 raw29314step0; decide +kernel
      have hl : raw29314step1Labels = raw29314step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29314step0 raw29314step0Labels permutation44 permutation4
    mixedMoment B raw29314step1 raw29314step1Labels = mixedMoment B raw29314step2 raw29314step2Labels := by
      have ha : raw29314step2 = -raw29314step1 := by apply Matrix.ext; change ∀ i j, raw29314step2 i j = -(raw29314step1 i j); unfold raw29314step2 raw29314step1; decide +kernel
      have hl : raw29314step2Labels = raw29314step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2274 node2274Labels := by rfl

def raw29315 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw29315step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29315step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw29315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29315 raw29315Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw29315 raw29315Labels = mixedMoment B raw29315step0 raw29315step0Labels := by
      have ha : raw29315step0 = (fun i j => raw29315 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29315step0 raw29315; decide +kernel
      have hl : raw29315step0Labels = raw29315Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29315 raw29315Labels permutation164 permutation4
    mixedMoment B raw29315step0 raw29315step0Labels = mixedMoment B raw29315step1 raw29315step1Labels := by
      have ha : raw29315step1 = -raw29315step0 := by apply Matrix.ext; change ∀ i j, raw29315step1 i j = -(raw29315step0 i j); unfold raw29315step1 raw29315step0; decide +kernel
      have hl : raw29315step1Labels = raw29315step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2213 node2213Labels := by rfl

def raw29316 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29316step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29316step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29316step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29316 raw29316Labels = mixedMoment B node2217 node2217Labels := by
  calc
    mixedMoment B raw29316 raw29316Labels = mixedMoment B raw29316step0 raw29316step0Labels := by
      have hz : ∀ j, raw29316 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29316step0 = (fun i j => raw29316 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29316step0 raw29316; decide +kernel
      have hl : raw29316step0Labels = raw29316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29316 raw29316Labels permutation346 hz
    mixedMoment B raw29316step0 raw29316step0Labels = mixedMoment B raw29316step1 raw29316step1Labels := by
      have ha : raw29316step1 = (fun i j => raw29316step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29316step1 raw29316step0; decide +kernel
      have hl : raw29316step1Labels = raw29316step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29316step0 raw29316step0Labels permutation35 permutation4
    mixedMoment B raw29316step1 raw29316step1Labels = mixedMoment B raw29316step2 raw29316step2Labels := by
      have ha : raw29316step2 = -raw29316step1 := by apply Matrix.ext; change ∀ i j, raw29316step2 i j = -(raw29316step1 i j); unfold raw29316step2 raw29316step1; decide +kernel
      have hl : raw29316step2Labels = raw29316step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2217 node2217Labels := by rfl

def raw29317 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29317step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29317 raw29317Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw29317 raw29317Labels = mixedMoment B raw29317step0 raw29317step0Labels := by
      have hz : ∀ j, raw29317 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29317step0 = (fun i j => raw29317 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29317step0 raw29317; decide +kernel
      have hl : raw29317step0Labels = raw29317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29317 raw29317Labels permutation346 hz
    mixedMoment B raw29317step0 raw29317step0Labels = mixedMoment B raw29317step1 raw29317step1Labels := by
      have ha : raw29317step1 = (fun i j => raw29317step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29317step1 raw29317step0; decide +kernel
      have hl : raw29317step1Labels = raw29317step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29317step0 raw29317step0Labels permutation32 permutation4
    mixedMoment B raw29317step1 raw29317step1Labels = mixedMoment B raw29317step2 raw29317step2Labels := by
      have ha : raw29317step2 = -raw29317step1 := by apply Matrix.ext; change ∀ i j, raw29317step2 i j = -(raw29317step1 i j); unfold raw29317step2 raw29317step1; decide +kernel
      have hl : raw29317step2Labels = raw29317step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2225 node2225Labels := by rfl

def raw29318 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29318step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw29318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw29318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29318 raw29318Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw29318 raw29318Labels = mixedMoment B raw29318step0 raw29318step0Labels := by
      have hz : ∀ j, raw29318 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29318step0 = (fun i j => raw29318 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29318step0 raw29318; decide +kernel
      have hl : raw29318step0Labels = raw29318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29318 raw29318Labels permutation346 hz
    mixedMoment B raw29318step0 raw29318step0Labels = mixedMoment B raw29318step1 raw29318step1Labels := by
      have ha : raw29318step1 = (fun i j => raw29318step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29318step1 raw29318step0; decide +kernel
      have hl : raw29318step1Labels = raw29318step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29318step0 raw29318step0Labels permutation34 permutation4
    mixedMoment B raw29318step1 raw29318step1Labels = mixedMoment B raw29318step2 raw29318step2Labels := by
      have ha : raw29318step2 = -raw29318step1 := by apply Matrix.ext; change ∀ i j, raw29318step2 i j = -(raw29318step1 i j); unfold raw29318step2 raw29318step1; decide +kernel
      have hl : raw29318step2Labels = raw29318step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2215 node2215Labels := by rfl

def raw29319 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![0, 0], ![0, 0], ![-2, 2], ![-2, 2]]
def raw29319Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29319step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![0, 0], ![-2, 2], ![-2, 2]]
def raw29319step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29319step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw29319step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29319step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw29319step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29319 raw29319Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw29319 raw29319Labels = mixedMoment B raw29319step0 raw29319step0Labels := by
      have hz : ∀ j, raw29319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29319step0 = (fun i j => raw29319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29319step0 raw29319; decide +kernel
      have hl : raw29319step0Labels = raw29319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29319 raw29319Labels permutation434 hz
    mixedMoment B raw29319step0 raw29319step0Labels = mixedMoment B raw29319step1 raw29319step1Labels := by
      have hz : ∀ j, raw29319step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29319step1 = (fun i j => raw29319step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29319step1 raw29319step0; decide +kernel
      have hl : raw29319step1Labels = raw29319step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29319step0 raw29319step0Labels permutation80 hz
    mixedMoment B raw29319step1 raw29319step1Labels = mixedMoment B raw29319step2 raw29319step2Labels := by
      have ha : raw29319step2 = -raw29319step1 := by apply Matrix.ext; change ∀ i j, raw29319step2 i j = -(raw29319step1 i j); unfold raw29319step2 raw29319step1; decide +kernel
      have hl : raw29319step2Labels = raw29319step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw29320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29320step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29320 raw29320Labels = mixedMoment B node1794 node1794Labels := by
  calc
    mixedMoment B raw29320 raw29320Labels = mixedMoment B raw29320step0 raw29320step0Labels := by
      have ha : raw29320step0 = (fun i j => raw29320 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29320step0 raw29320; decide +kernel
      have hl : raw29320step0Labels = raw29320Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29320 raw29320Labels permutation158 permutation2
    _ = mixedMoment B node1794 node1794Labels := by rfl

def raw29321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29321 raw29321Labels = mixedMoment B node2012 node2012Labels := by
  calc
    _ = mixedMoment B node2012 node2012Labels := by rfl

def raw29322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29322Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29322step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29322 raw29322Labels = mixedMoment B node1977 node1977Labels := by
  calc
    mixedMoment B raw29322 raw29322Labels = mixedMoment B raw29322step0 raw29322step0Labels := by
      have ha : raw29322step0 = (fun i j => raw29322 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29322step0 raw29322; decide +kernel
      have hl : raw29322step0Labels = raw29322Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29322 raw29322Labels permutation158 permutation2
    _ = mixedMoment B node1977 node1977Labels := by rfl

def raw29323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw29323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29323 raw29323Labels = mixedMoment B node2023 node2023Labels := by
  calc
    mixedMoment B raw29323 raw29323Labels = mixedMoment B raw29323step0 raw29323step0Labels := by
      have ha : raw29323step0 = (fun i j => raw29323 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29323step0 raw29323; decide +kernel
      have hl : raw29323step0Labels = raw29323Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29323 raw29323Labels permutation159 permutation2
    _ = mixedMoment B node2023 node2023Labels := by rfl

def raw29324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29324Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29324step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29324step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29324 raw29324Labels = mixedMoment B node3199 node3199Labels := by
  calc
    mixedMoment B raw29324 raw29324Labels = mixedMoment B raw29324step0 raw29324step0Labels := by
      have ha : raw29324step0 = (fun i j => raw29324 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29324step0 raw29324; decide +kernel
      have hl : raw29324step0Labels = raw29324Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29324 raw29324Labels permutation177 permutation2
    _ = mixedMoment B node3199 node3199Labels := by rfl

def raw29325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29325Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29325 raw29325Labels = mixedMoment B node3189 node3189Labels := by
  calc
    mixedMoment B raw29325 raw29325Labels = mixedMoment B raw29325step0 raw29325step0Labels := by
      have ha : raw29325step0 = (fun i j => raw29325 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29325step0 raw29325; decide +kernel
      have hl : raw29325step0Labels = raw29325Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29325 raw29325Labels permutation153 permutation2
    _ = mixedMoment B node3189 node3189Labels := by rfl

def raw29326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29326Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29326step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw29326step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29326step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw29326step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29326 raw29326Labels = mixedMoment B node2323 node2323Labels := by
  calc
    mixedMoment B raw29326 raw29326Labels = mixedMoment B raw29326step0 raw29326step0Labels := by
      have ha : raw29326step0 = (fun i j => raw29326 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29326step0 raw29326; decide +kernel
      have hl : raw29326step0Labels = raw29326Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29326 raw29326Labels permutation587 permutation2
    mixedMoment B raw29326step0 raw29326step0Labels = mixedMoment B raw29326step1 raw29326step1Labels := by
      have ha : raw29326step1 = -raw29326step0 := by apply Matrix.ext; change ∀ i j, raw29326step1 i j = -(raw29326step0 i j); unfold raw29326step1 raw29326step0; decide +kernel
      have hl : raw29326step1Labels = raw29326step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2323 node2323Labels := by rfl

def raw29327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29327Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29327step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw29327step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29327step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw29327step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29327 raw29327Labels = mixedMoment B node2800 node2800Labels := by
  calc
    mixedMoment B raw29327 raw29327Labels = mixedMoment B raw29327step0 raw29327step0Labels := by
      have ha : raw29327step0 = (fun i j => raw29327 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29327step0 raw29327; decide +kernel
      have hl : raw29327step0Labels = raw29327Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29327 raw29327Labels permutation686 permutation2
    mixedMoment B raw29327step0 raw29327step0Labels = mixedMoment B raw29327step1 raw29327step1Labels := by
      have ha : raw29327step1 = -raw29327step0 := by apply Matrix.ext; change ∀ i j, raw29327step1 i j = -(raw29327step0 i j); unfold raw29327step1 raw29327step0; decide +kernel
      have hl : raw29327step1Labels = raw29327step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2800 node2800Labels := by rfl

def raw29328 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29328Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw29328step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw29328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29328 raw29328Labels = mixedMoment B node3476 node3476Labels := by
  calc
    mixedMoment B raw29328 raw29328Labels = mixedMoment B raw29328step0 raw29328step0Labels := by
      have ha : raw29328step0 = (fun i j => raw29328 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29328step0 raw29328; decide +kernel
      have hl : raw29328step0Labels = raw29328Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29328 raw29328Labels permutation164 permutation4
    mixedMoment B raw29328step0 raw29328step0Labels = mixedMoment B raw29328step1 raw29328step1Labels := by
      have ha : raw29328step1 = -raw29328step0 := by apply Matrix.ext; change ∀ i j, raw29328step1 i j = -(raw29328step0 i j); unfold raw29328step1 raw29328step0; decide +kernel
      have hl : raw29328step1Labels = raw29328step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3476 node3476Labels := by rfl

def raw29329 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29329Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29329step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw29329step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw29329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29329 raw29329Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw29329 raw29329Labels = mixedMoment B raw29329step0 raw29329step0Labels := by
      have hz : ∀ j, raw29329 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29329step0 = (fun i j => raw29329 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29329step0 raw29329; decide +kernel
      have hl : raw29329step0Labels = raw29329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29329 raw29329Labels permutation434 hz
    mixedMoment B raw29329step0 raw29329step0Labels = mixedMoment B raw29329step1 raw29329step1Labels := by
      have ha : raw29329step1 = (fun i j => raw29329step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29329step1 raw29329step0; decide +kernel
      have hl : raw29329step1Labels = raw29329step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29329step0 raw29329step0Labels permutation34 permutation4
    mixedMoment B raw29329step1 raw29329step1Labels = mixedMoment B raw29329step2 raw29329step2Labels := by
      have ha : raw29329step2 = -raw29329step1 := by apply Matrix.ext; change ∀ i j, raw29329step2 i j = -(raw29329step1 i j); unfold raw29329step2 raw29329step1; decide +kernel
      have hl : raw29329step2Labels = raw29329step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3612 node3612Labels := by rfl

def raw29330 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29330step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw29330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29330 raw29330Labels = mixedMoment B node2396 node2396Labels := by
  calc
    mixedMoment B raw29330 raw29330Labels = mixedMoment B raw29330step0 raw29330step0Labels := by
      have ha : raw29330step0 = (fun i j => raw29330 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29330step0 raw29330; decide +kernel
      have hl : raw29330step0Labels = raw29330Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29330 raw29330Labels permutation584 permutation2
    _ = mixedMoment B node2396 node2396Labels := by rfl

def raw29331 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw29331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29331step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw29331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29331 raw29331Labels = mixedMoment B node3610 node3610Labels := by
  calc
    mixedMoment B raw29331 raw29331Labels = mixedMoment B raw29331step0 raw29331step0Labels := by
      have ha : raw29331step0 = (fun i j => raw29331 (permutation168 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29331step0 raw29331; decide +kernel
      have hl : raw29331step0Labels = raw29331Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29331 raw29331Labels permutation168 permutation4
    mixedMoment B raw29331step0 raw29331step0Labels = mixedMoment B raw29331step1 raw29331step1Labels := by
      have ha : raw29331step1 = -raw29331step0 := by apply Matrix.ext; change ∀ i j, raw29331step1 i j = -(raw29331step0 i j); unfold raw29331step1 raw29331step0; decide +kernel
      have hl : raw29331step1Labels = raw29331step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3610 node3610Labels := by rfl

def raw29332 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29332Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw29332step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29332step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw29332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29332 raw29332Labels = mixedMoment B node2269 node2269Labels := by
  calc
    mixedMoment B raw29332 raw29332Labels = mixedMoment B raw29332step0 raw29332step0Labels := by
      have ha : raw29332step0 = (fun i j => raw29332 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29332step0 raw29332; decide +kernel
      have hl : raw29332step0Labels = raw29332Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29332 raw29332Labels permutation240 permutation4
    mixedMoment B raw29332step0 raw29332step0Labels = mixedMoment B raw29332step1 raw29332step1Labels := by
      have ha : raw29332step1 = -raw29332step0 := by apply Matrix.ext; change ∀ i j, raw29332step1 i j = -(raw29332step0 i j); unfold raw29332step1 raw29332step0; decide +kernel
      have hl : raw29332step1Labels = raw29332step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2269 node2269Labels := by rfl

def raw29333 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29333Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29333step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw29333step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29333step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw29333step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29333 raw29333Labels = mixedMoment B node2209 node2209Labels := by
  calc
    mixedMoment B raw29333 raw29333Labels = mixedMoment B raw29333step0 raw29333step0Labels := by
      have ha : raw29333step0 = (fun i j => raw29333 (permutation169 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29333step0 raw29333; decide +kernel
      have hl : raw29333step0Labels = raw29333Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29333 raw29333Labels permutation169 permutation4
    mixedMoment B raw29333step0 raw29333step0Labels = mixedMoment B raw29333step1 raw29333step1Labels := by
      have ha : raw29333step1 = -raw29333step0 := by apply Matrix.ext; change ∀ i j, raw29333step1 i j = -(raw29333step0 i j); unfold raw29333step1 raw29333step0; decide +kernel
      have hl : raw29333step1Labels = raw29333step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2209 node2209Labels := by rfl

def raw29334 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29334Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw29334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29334step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw29334step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29334 raw29334Labels = mixedMoment B node2209 node2209Labels := by
  calc
    mixedMoment B raw29334 raw29334Labels = mixedMoment B raw29334step0 raw29334step0Labels := by
      have ha : raw29334step0 = (fun i j => raw29334 (permutation168 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29334step0 raw29334; decide +kernel
      have hl : raw29334step0Labels = raw29334Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29334 raw29334Labels permutation168 permutation4
    mixedMoment B raw29334step0 raw29334step0Labels = mixedMoment B raw29334step1 raw29334step1Labels := by
      have ha : raw29334step1 = -raw29334step0 := by apply Matrix.ext; change ∀ i j, raw29334step1 i j = -(raw29334step0 i j); unfold raw29334step1 raw29334step0; decide +kernel
      have hl : raw29334step1Labels = raw29334step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2209 node2209Labels := by rfl

def raw29335 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw29335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29335step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw29335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29335 raw29335Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw29335 raw29335Labels = mixedMoment B raw29335step0 raw29335step0Labels := by
      have ha : raw29335step0 = (fun i j => raw29335 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29335step0 raw29335; decide +kernel
      have hl : raw29335step0Labels = raw29335Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29335 raw29335Labels permutation170 permutation4
    mixedMoment B raw29335step0 raw29335step0Labels = mixedMoment B raw29335step1 raw29335step1Labels := by
      have ha : raw29335step1 = -raw29335step0 := by apply Matrix.ext; change ∀ i j, raw29335step1 i j = -(raw29335step0 i j); unfold raw29335step1 raw29335step0; decide +kernel
      have hl : raw29335step1Labels = raw29335step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2213 node2213Labels := by rfl

def raw29336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29336 raw29336Labels = mixedMoment B node3193 node3193Labels := by
  calc
    mixedMoment B raw29336 raw29336Labels = mixedMoment B raw29336step0 raw29336step0Labels := by
      have ha : raw29336step0 = (fun i j => raw29336 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29336step0 raw29336; decide +kernel
      have hl : raw29336step0Labels = raw29336Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29336 raw29336Labels permutation158 permutation2
    _ = mixedMoment B node3193 node3193Labels := by rfl

def raw29337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw29337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29337step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29337step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29337 raw29337Labels = mixedMoment B node3648 node3648Labels := by
  calc
    mixedMoment B raw29337 raw29337Labels = mixedMoment B raw29337step0 raw29337step0Labels := by
      have ha : raw29337step0 = (fun i j => raw29337 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29337step0 raw29337; decide +kernel
      have hl : raw29337step0Labels = raw29337Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29337 raw29337Labels permutation583 permutation2
    mixedMoment B raw29337step0 raw29337step0Labels = mixedMoment B raw29337step1 raw29337step1Labels := by
      have ha : raw29337step1 = -raw29337step0 := by apply Matrix.ext; change ∀ i j, raw29337step1 i j = -(raw29337step0 i j); unfold raw29337step1 raw29337step0; decide +kernel
      have hl : raw29337step1Labels = raw29337step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3648 node3648Labels := by rfl

def raw29338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw29338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29338 raw29338Labels = mixedMoment B node3659 node3659Labels := by
  calc
    mixedMoment B raw29338 raw29338Labels = mixedMoment B raw29338step0 raw29338step0Labels := by
      have ha : raw29338step0 = (fun i j => raw29338 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29338step0 raw29338; decide +kernel
      have hl : raw29338step0Labels = raw29338Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29338 raw29338Labels permutation587 permutation2
    mixedMoment B raw29338step0 raw29338step0Labels = mixedMoment B raw29338step1 raw29338step1Labels := by
      have ha : raw29338step1 = -raw29338step0 := by apply Matrix.ext; change ∀ i j, raw29338step1 i j = -(raw29338step0 i j); unfold raw29338step1 raw29338step0; decide +kernel
      have hl : raw29338step1Labels = raw29338step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3659 node3659Labels := by rfl

def raw29339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw29339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29339step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw29339step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29339 raw29339Labels = mixedMoment B node3653 node3653Labels := by
  calc
    mixedMoment B raw29339 raw29339Labels = mixedMoment B raw29339step0 raw29339step0Labels := by
      have ha : raw29339step0 = (fun i j => raw29339 (permutation582 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29339step0 raw29339; decide +kernel
      have hl : raw29339step0Labels = raw29339Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29339 raw29339Labels permutation582 permutation2
    mixedMoment B raw29339step0 raw29339step0Labels = mixedMoment B raw29339step1 raw29339step1Labels := by
      have ha : raw29339step1 = -raw29339step0 := by apply Matrix.ext; change ∀ i j, raw29339step1 i j = -(raw29339step0 i j); unfold raw29339step1 raw29339step0; decide +kernel
      have hl : raw29339step1Labels = raw29339step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3653 node3653Labels := by rfl

def raw29340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw29340Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw29340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29340step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw29340step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29340 raw29340Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw29340 raw29340Labels = mixedMoment B raw29340step0 raw29340step0Labels := by
      have ha : raw29340step0 = (fun i j => raw29340 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29340step0 raw29340; decide +kernel
      have hl : raw29340step0Labels = raw29340Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29340 raw29340Labels permutation682 permutation2
    mixedMoment B raw29340step0 raw29340step0Labels = mixedMoment B raw29340step1 raw29340step1Labels := by
      have ha : raw29340step1 = -raw29340step0 := by apply Matrix.ext; change ∀ i j, raw29340step1 i j = -(raw29340step0 i j); unfold raw29340step1 raw29340step0; decide +kernel
      have hl : raw29340step1Labels = raw29340step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3762 node3762Labels := by rfl

def raw29341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw29341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw29341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29341step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw29341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29341 raw29341Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw29341 raw29341Labels = mixedMoment B raw29341step0 raw29341step0Labels := by
      have ha : raw29341step0 = (fun i j => raw29341 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29341step0 raw29341; decide +kernel
      have hl : raw29341step0Labels = raw29341Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29341 raw29341Labels permutation584 permutation2
    mixedMoment B raw29341step0 raw29341step0Labels = mixedMoment B raw29341step1 raw29341step1Labels := by
      have ha : raw29341step1 = -raw29341step0 := by apply Matrix.ext; change ∀ i j, raw29341step1 i j = -(raw29341step0 i j); unfold raw29341step1 raw29341step0; decide +kernel
      have hl : raw29341step1Labels = raw29341step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3762 node3762Labels := by rfl

def raw29342 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-2, 2], ![2, -2], ![2, -2]]
def raw29342Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29342step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![2, -2], ![2, -2]]
def raw29342step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29342step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw29342step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29342step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw29342step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29342 raw29342Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw29342 raw29342Labels = mixedMoment B raw29342step0 raw29342step0Labels := by
      have hz : ∀ j, raw29342 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw29342step0 = (fun i j => raw29342 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw29342step0 raw29342; decide +kernel
      have hl : raw29342step0Labels = raw29342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29342 raw29342Labels permutation152 hz
    mixedMoment B raw29342step0 raw29342step0Labels = mixedMoment B raw29342step1 raw29342step1Labels := by
      have ha : raw29342step1 = (fun i j => raw29342step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29342step1 raw29342step0; decide +kernel
      have hl : raw29342step1Labels = raw29342step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29342step0 raw29342step0Labels permutation122 permutation0
    mixedMoment B raw29342step1 raw29342step1Labels = mixedMoment B raw29342step2 raw29342step2Labels := by
      have ha : raw29342step2 = -raw29342step1 := by apply Matrix.ext; change ∀ i j, raw29342step2 i j = -(raw29342step1 i j); unfold raw29342step2 raw29342step1; decide +kernel
      have hl : raw29342step2Labels = raw29342step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw29343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29343Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29343step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29343 raw29343Labels = mixedMoment B node1829 node1829Labels := by
  calc
    mixedMoment B raw29343 raw29343Labels = mixedMoment B raw29343step0 raw29343step0Labels := by
      have hz : ∀ j, raw29343 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29343step0 = (fun i j => raw29343 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29343step0 raw29343; decide +kernel
      have hl : raw29343step0Labels = raw29343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29343 raw29343Labels permutation346 hz
    _ = mixedMoment B node1829 node1829Labels := by rfl

def raw29344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29344Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29344step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29344step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29344 raw29344Labels = mixedMoment B node1977 node1977Labels := by
  calc
    mixedMoment B raw29344 raw29344Labels = mixedMoment B raw29344step0 raw29344step0Labels := by
      have ha : raw29344step0 = (fun i j => raw29344 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29344step0 raw29344; decide +kernel
      have hl : raw29344step0Labels = raw29344Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29344 raw29344Labels permutation176 permutation2
    _ = mixedMoment B node1977 node1977Labels := by rfl

def raw29345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29345 raw29345Labels = mixedMoment B node2094 node2094Labels := by
  calc
    mixedMoment B raw29345 raw29345Labels = mixedMoment B raw29345step0 raw29345step0Labels := by
      have hz : ∀ j, raw29345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29345step0 = (fun i j => raw29345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29345step0 raw29345; decide +kernel
      have hl : raw29345step0Labels = raw29345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29345 raw29345Labels permutation346 hz
    _ = mixedMoment B node2094 node2094Labels := by rfl

def raw29346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw29346Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw29346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29346 raw29346Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw29346 raw29346Labels = mixedMoment B raw29346step0 raw29346step0Labels := by
      have hz : ∀ j, raw29346 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29346step0 = (fun i j => raw29346 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29346step0 raw29346; decide +kernel
      have hl : raw29346step0Labels = raw29346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29346 raw29346Labels permutation346 hz
    mixedMoment B raw29346step0 raw29346step0Labels = mixedMoment B raw29346step1 raw29346step1Labels := by
      have ha : raw29346step1 = (fun i j => raw29346step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29346step1 raw29346step0; decide +kernel
      have hl : raw29346step1Labels = raw29346step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29346step0 raw29346step0Labels permutation33 permutation2
    _ = mixedMoment B node2110 node2110Labels := by rfl

def raw29347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29347Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29347 raw29347Labels = mixedMoment B node3133 node3133Labels := by
  calc
    mixedMoment B raw29347 raw29347Labels = mixedMoment B raw29347step0 raw29347step0Labels := by
      have ha : raw29347step0 = (fun i j => raw29347 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29347step0 raw29347; decide +kernel
      have hl : raw29347step0Labels = raw29347Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29347 raw29347Labels permutation159 permutation2
    _ = mixedMoment B node3133 node3133Labels := by rfl

def raw29348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29348Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29348step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29348 raw29348Labels = mixedMoment B node3138 node3138Labels := by
  calc
    mixedMoment B raw29348 raw29348Labels = mixedMoment B raw29348step0 raw29348step0Labels := by
      have hz : ∀ j, raw29348 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29348step0 = (fun i j => raw29348 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29348step0 raw29348; decide +kernel
      have hl : raw29348step0Labels = raw29348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29348 raw29348Labels permutation346 hz
    mixedMoment B raw29348step0 raw29348step0Labels = mixedMoment B raw29348step1 raw29348step1Labels := by
      have ha : raw29348step1 = (fun i j => raw29348step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29348step1 raw29348step0; decide +kernel
      have hl : raw29348step1Labels = raw29348step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29348step0 raw29348step0Labels permutation33 permutation2
    _ = mixedMoment B node3138 node3138Labels := by rfl

def raw29349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29349Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29349step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw29349step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29349step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw29349step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29349 raw29349Labels = mixedMoment B node2327 node2327Labels := by
  calc
    mixedMoment B raw29349 raw29349Labels = mixedMoment B raw29349step0 raw29349step0Labels := by
      have hz : ∀ j, raw29349 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29349step0 = (fun i j => raw29349 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29349step0 raw29349; decide +kernel
      have hl : raw29349step0Labels = raw29349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29349 raw29349Labels permutation346 hz
    mixedMoment B raw29349step0 raw29349step0Labels = mixedMoment B raw29349step1 raw29349step1Labels := by
      have ha : raw29349step1 = (fun i j => raw29349step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29349step1 raw29349step0; decide +kernel
      have hl : raw29349step1Labels = raw29349step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29349step0 raw29349step0Labels permutation127 permutation2
    mixedMoment B raw29349step1 raw29349step1Labels = mixedMoment B raw29349step2 raw29349step2Labels := by
      have ha : raw29349step2 = -raw29349step1 := by apply Matrix.ext; change ∀ i j, raw29349step2 i j = -(raw29349step1 i j); unfold raw29349step2 raw29349step1; decide +kernel
      have hl : raw29349step2Labels = raw29349step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2327 node2327Labels := by rfl

def raw29350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29350Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29350step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw29350step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw29350step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29350 raw29350Labels = mixedMoment B node2803 node2803Labels := by
  calc
    mixedMoment B raw29350 raw29350Labels = mixedMoment B raw29350step0 raw29350step0Labels := by
      have hz : ∀ j, raw29350 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29350step0 = (fun i j => raw29350 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29350step0 raw29350; decide +kernel
      have hl : raw29350step0Labels = raw29350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29350 raw29350Labels permutation346 hz
    mixedMoment B raw29350step0 raw29350step0Labels = mixedMoment B raw29350step1 raw29350step1Labels := by
      have ha : raw29350step1 = (fun i j => raw29350step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29350step1 raw29350step0; decide +kernel
      have hl : raw29350step1Labels = raw29350step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29350step0 raw29350step0Labels permutation151 permutation2
    mixedMoment B raw29350step1 raw29350step1Labels = mixedMoment B raw29350step2 raw29350step2Labels := by
      have ha : raw29350step2 = -raw29350step1 := by apply Matrix.ext; change ∀ i j, raw29350step2 i j = -(raw29350step1 i j); unfold raw29350step2 raw29350step1; decide +kernel
      have hl : raw29350step2Labels = raw29350step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2803 node2803Labels := by rfl

def raw29351 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29351Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw29351step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29351step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw29351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29351 raw29351Labels = mixedMoment B node3536 node3536Labels := by
  calc
    mixedMoment B raw29351 raw29351Labels = mixedMoment B raw29351step0 raw29351step0Labels := by
      have ha : raw29351step0 = (fun i j => raw29351 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29351step0 raw29351; decide +kernel
      have hl : raw29351step0Labels = raw29351Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29351 raw29351Labels permutation188 permutation4
    mixedMoment B raw29351step0 raw29351step0Labels = mixedMoment B raw29351step1 raw29351step1Labels := by
      have ha : raw29351step1 = -raw29351step0 := by apply Matrix.ext; change ∀ i j, raw29351step1 i j = -(raw29351step0 i j); unfold raw29351step1 raw29351step0; decide +kernel
      have hl : raw29351step1Labels = raw29351step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3536 node3536Labels := by rfl

def raw29352 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29352Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29352step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29352step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw29352step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29352step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, -1, 2]]
def raw29352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29352step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw29352step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29352 raw29352Labels = mixedMoment B node3631 node3631Labels := by
  calc
    mixedMoment B raw29352 raw29352Labels = mixedMoment B raw29352step0 raw29352step0Labels := by
      have hz : ∀ j, raw29352 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29352step0 = (fun i j => raw29352 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29352step0 raw29352; decide +kernel
      have hl : raw29352step0Labels = raw29352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29352 raw29352Labels permutation434 hz
    mixedMoment B raw29352step0 raw29352step0Labels = mixedMoment B raw29352step1 raw29352step1Labels := by
      have hz : ∀ j, raw29352step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29352step1 = (fun i j => raw29352step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29352step1 raw29352step0; decide +kernel
      have hl : raw29352step1Labels = raw29352step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29352step0 raw29352step0Labels permutation80 hz
    mixedMoment B raw29352step1 raw29352step1Labels = mixedMoment B raw29352step2 raw29352step2Labels := by
      have ha : raw29352step2 = (fun i j => raw29352step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29352step2 raw29352step1; decide +kernel
      have hl : raw29352step2Labels = raw29352step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29352step1 raw29352step1Labels permutation10 permutation4
    mixedMoment B raw29352step2 raw29352step2Labels = mixedMoment B raw29352step3 raw29352step3Labels := by
      have ha : raw29352step3 = -raw29352step2 := by apply Matrix.ext; change ∀ i j, raw29352step3 i j = -(raw29352step2 i j); unfold raw29352step3 raw29352step2; decide +kernel
      have hl : raw29352step3Labels = raw29352step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3631 node3631Labels := by rfl

def raw29353 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29353Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29353step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw29353step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29353 raw29353Labels = mixedMoment B node2401 node2401Labels := by
  calc
    mixedMoment B raw29353 raw29353Labels = mixedMoment B raw29353step0 raw29353step0Labels := by
      have hz : ∀ j, raw29353 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29353step0 = (fun i j => raw29353 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29353step0 raw29353; decide +kernel
      have hl : raw29353step0Labels = raw29353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29353 raw29353Labels permutation346 hz
    mixedMoment B raw29353step0 raw29353step0Labels = mixedMoment B raw29353step1 raw29353step1Labels := by
      have ha : raw29353step1 = (fun i j => raw29353step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29353step1 raw29353step0; decide +kernel
      have hl : raw29353step1Labels = raw29353step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29353step0 raw29353step0Labels permutation126 permutation2
    _ = mixedMoment B node2401 node2401Labels := by rfl

def raw29354 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29354Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29354step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -2, 2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0]]
def raw29354step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29354step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0]]
def raw29354step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29354 raw29354Labels = mixedMoment B node3630 node3630Labels := by
  calc
    mixedMoment B raw29354 raw29354Labels = mixedMoment B raw29354step0 raw29354step0Labels := by
      have hz : ∀ j, raw29354 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29354step0 = (fun i j => raw29354 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29354step0 raw29354; decide +kernel
      have hl : raw29354step0Labels = raw29354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29354 raw29354Labels permutation346 hz
    mixedMoment B raw29354step0 raw29354step0Labels = mixedMoment B raw29354step1 raw29354step1Labels := by
      have ha : raw29354step1 = (fun i j => raw29354step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29354step1 raw29354step0; decide +kernel
      have hl : raw29354step1Labels = raw29354step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29354step0 raw29354step0Labels permutation48 permutation4
    mixedMoment B raw29354step1 raw29354step1Labels = mixedMoment B raw29354step2 raw29354step2Labels := by
      have ha : raw29354step2 = -raw29354step1 := by apply Matrix.ext; change ∀ i j, raw29354step2 i j = -(raw29354step1 i j); unfold raw29354step2 raw29354step1; decide +kernel
      have hl : raw29354step2Labels = raw29354step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3630 node3630Labels := by rfl

def raw29355 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29355Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29355step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29355step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw29355step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29355step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, -1, 2], ![-2, 3, -1]]
def raw29355step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29355step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw29355step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29355 raw29355Labels = mixedMoment B node2280 node2280Labels := by
  calc
    mixedMoment B raw29355 raw29355Labels = mixedMoment B raw29355step0 raw29355step0Labels := by
      have hz : ∀ j, raw29355 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29355step0 = (fun i j => raw29355 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29355step0 raw29355; decide +kernel
      have hl : raw29355step0Labels = raw29355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29355 raw29355Labels permutation434 hz
    mixedMoment B raw29355step0 raw29355step0Labels = mixedMoment B raw29355step1 raw29355step1Labels := by
      have hz : ∀ j, raw29355step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29355step1 = (fun i j => raw29355step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29355step1 raw29355step0; decide +kernel
      have hl : raw29355step1Labels = raw29355step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29355step0 raw29355step0Labels permutation80 hz
    mixedMoment B raw29355step1 raw29355step1Labels = mixedMoment B raw29355step2 raw29355step2Labels := by
      have ha : raw29355step2 = (fun i j => raw29355step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29355step2 raw29355step1; decide +kernel
      have hl : raw29355step2Labels = raw29355step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29355step1 raw29355step1Labels permutation11 permutation4
    mixedMoment B raw29355step2 raw29355step2Labels = mixedMoment B raw29355step3 raw29355step3Labels := by
      have ha : raw29355step3 = -raw29355step2 := by apply Matrix.ext; change ∀ i j, raw29355step3 i j = -(raw29355step2 i j); unfold raw29355step3 raw29355step2; decide +kernel
      have hl : raw29355step3Labels = raw29355step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2280 node2280Labels := by rfl

def raw29356 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29356step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw29356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29356step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw29356step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29356 raw29356Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw29356 raw29356Labels = mixedMoment B raw29356step0 raw29356step0Labels := by
      have hz : ∀ j, raw29356 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29356step0 = (fun i j => raw29356 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29356step0 raw29356; decide +kernel
      have hl : raw29356step0Labels = raw29356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29356 raw29356Labels permutation434 hz
    mixedMoment B raw29356step0 raw29356step0Labels = mixedMoment B raw29356step1 raw29356step1Labels := by
      have ha : raw29356step1 = (fun i j => raw29356step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29356step1 raw29356step0; decide +kernel
      have hl : raw29356step1Labels = raw29356step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29356step0 raw29356step0Labels permutation44 permutation4
    mixedMoment B raw29356step1 raw29356step1Labels = mixedMoment B raw29356step2 raw29356step2Labels := by
      have ha : raw29356step2 = -raw29356step1 := by apply Matrix.ext; change ∀ i j, raw29356step2 i j = -(raw29356step1 i j); unfold raw29356step2 raw29356step1; decide +kernel
      have hl : raw29356step2Labels = raw29356step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2274 node2274Labels := by rfl

def raw29357 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29357Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29357step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29357step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29357step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw29357step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29357step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw29357step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29357 raw29357Labels = mixedMoment B node2288 node2288Labels := by
  calc
    mixedMoment B raw29357 raw29357Labels = mixedMoment B raw29357step0 raw29357step0Labels := by
      have hz : ∀ j, raw29357 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29357step0 = (fun i j => raw29357 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29357step0 raw29357; decide +kernel
      have hl : raw29357step0Labels = raw29357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29357 raw29357Labels permutation434 hz
    mixedMoment B raw29357step0 raw29357step0Labels = mixedMoment B raw29357step1 raw29357step1Labels := by
      have hz : ∀ j, raw29357step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29357step1 = (fun i j => raw29357step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29357step1 raw29357step0; decide +kernel
      have hl : raw29357step1Labels = raw29357step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29357step0 raw29357step0Labels permutation80 hz
    mixedMoment B raw29357step1 raw29357step1Labels = mixedMoment B raw29357step2 raw29357step2Labels := by
      have ha : raw29357step2 = (fun i j => raw29357step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29357step2 raw29357step1; decide +kernel
      have hl : raw29357step2Labels = raw29357step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29357step1 raw29357step1Labels permutation8 permutation4
    mixedMoment B raw29357step2 raw29357step2Labels = mixedMoment B raw29357step3 raw29357step3Labels := by
      have ha : raw29357step3 = -raw29357step2 := by apply Matrix.ext; change ∀ i j, raw29357step3 i j = -(raw29357step2 i j); unfold raw29357step3 raw29357step2; decide +kernel
      have hl : raw29357step3Labels = raw29357step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2288 node2288Labels := by rfl

def raw29358 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29358Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29358step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29358step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw29358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29358step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw29358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29358step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw29358step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29358 raw29358Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw29358 raw29358Labels = mixedMoment B raw29358step0 raw29358step0Labels := by
      have hz : ∀ j, raw29358 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29358step0 = (fun i j => raw29358 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29358step0 raw29358; decide +kernel
      have hl : raw29358step0Labels = raw29358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29358 raw29358Labels permutation434 hz
    mixedMoment B raw29358step0 raw29358step0Labels = mixedMoment B raw29358step1 raw29358step1Labels := by
      have hz : ∀ j, raw29358step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29358step1 = (fun i j => raw29358step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29358step1 raw29358step0; decide +kernel
      have hl : raw29358step1Labels = raw29358step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29358step0 raw29358step0Labels permutation80 hz
    mixedMoment B raw29358step1 raw29358step1Labels = mixedMoment B raw29358step2 raw29358step2Labels := by
      have ha : raw29358step2 = (fun i j => raw29358step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29358step2 raw29358step1; decide +kernel
      have hl : raw29358step2Labels = raw29358step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29358step1 raw29358step1Labels permutation10 permutation4
    mixedMoment B raw29358step2 raw29358step2Labels = mixedMoment B raw29358step3 raw29358step3Labels := by
      have ha : raw29358step3 = -raw29358step2 := by apply Matrix.ext; change ∀ i j, raw29358step3 i j = -(raw29358step2 i j); unfold raw29358step3 raw29358step2; decide +kernel
      have hl : raw29358step3Labels = raw29358step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2276 node2276Labels := by rfl

def raw29359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29359Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29359 raw29359Labels = mixedMoment B node3166 node3166Labels := by
  calc
    mixedMoment B raw29359 raw29359Labels = mixedMoment B raw29359step0 raw29359step0Labels := by
      have hz : ∀ j, raw29359 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29359step0 = (fun i j => raw29359 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29359step0 raw29359; decide +kernel
      have hl : raw29359step0Labels = raw29359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29359 raw29359Labels permutation346 hz
    _ = mixedMoment B node3166 node3166Labels := by rfl

def raw29360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29360Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw29360step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29360step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw29360step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29360 raw29360Labels = mixedMoment B node3660 node3660Labels := by
  calc
    mixedMoment B raw29360 raw29360Labels = mixedMoment B raw29360step0 raw29360step0Labels := by
      have hz : ∀ j, raw29360 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29360step0 = (fun i j => raw29360 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29360step0 raw29360; decide +kernel
      have hl : raw29360step0Labels = raw29360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29360 raw29360Labels permutation346 hz
    mixedMoment B raw29360step0 raw29360step0Labels = mixedMoment B raw29360step1 raw29360step1Labels := by
      have ha : raw29360step1 = (fun i j => raw29360step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29360step1 raw29360step0; decide +kernel
      have hl : raw29360step1Labels = raw29360step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29360step0 raw29360step0Labels permutation126 permutation2
    mixedMoment B raw29360step1 raw29360step1Labels = mixedMoment B raw29360step2 raw29360step2Labels := by
      have ha : raw29360step2 = -raw29360step1 := by apply Matrix.ext; change ∀ i j, raw29360step2 i j = -(raw29360step1 i j); unfold raw29360step2 raw29360step1; decide +kernel
      have hl : raw29360step2Labels = raw29360step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3660 node3660Labels := by rfl

def raw29361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29361Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw29361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29361step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw29361step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29361 raw29361Labels = mixedMoment B node3658 node3658Labels := by
  calc
    mixedMoment B raw29361 raw29361Labels = mixedMoment B raw29361step0 raw29361step0Labels := by
      have ha : raw29361step0 = (fun i j => raw29361 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29361step0 raw29361; decide +kernel
      have hl : raw29361step0Labels = raw29361Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29361 raw29361Labels permutation589 permutation2
    mixedMoment B raw29361step0 raw29361step0Labels = mixedMoment B raw29361step1 raw29361step1Labels := by
      have ha : raw29361step1 = -raw29361step0 := by apply Matrix.ext; change ∀ i j, raw29361step1 i j = -(raw29361step0 i j); unfold raw29361step1 raw29361step0; decide +kernel
      have hl : raw29361step1Labels = raw29361step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3658 node3658Labels := by rfl

def raw29362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29362Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29362step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29362 raw29362Labels = mixedMoment B node3666 node3666Labels := by
  calc
    mixedMoment B raw29362 raw29362Labels = mixedMoment B raw29362step0 raw29362step0Labels := by
      have hz : ∀ j, raw29362 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29362step0 = (fun i j => raw29362 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29362step0 raw29362; decide +kernel
      have hl : raw29362step0Labels = raw29362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29362 raw29362Labels permutation346 hz
    mixedMoment B raw29362step0 raw29362step0Labels = mixedMoment B raw29362step1 raw29362step1Labels := by
      have ha : raw29362step1 = (fun i j => raw29362step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29362step1 raw29362step0; decide +kernel
      have hl : raw29362step1Labels = raw29362step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29362step0 raw29362step0Labels permutation125 permutation2
    mixedMoment B raw29362step1 raw29362step1Labels = mixedMoment B raw29362step2 raw29362step2Labels := by
      have ha : raw29362step2 = -raw29362step1 := by apply Matrix.ext; change ∀ i j, raw29362step2 i j = -(raw29362step1 i j); unfold raw29362step2 raw29362step1; decide +kernel
      have hl : raw29362step2Labels = raw29362step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3666 node3666Labels := by rfl

def raw29363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw29363Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw29363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29363step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29363 raw29363Labels = mixedMoment B node3772 node3772Labels := by
  calc
    mixedMoment B raw29363 raw29363Labels = mixedMoment B raw29363step0 raw29363step0Labels := by
      have hz : ∀ j, raw29363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29363step0 = (fun i j => raw29363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29363step0 raw29363; decide +kernel
      have hl : raw29363step0Labels = raw29363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29363 raw29363Labels permutation346 hz
    mixedMoment B raw29363step0 raw29363step0Labels = mixedMoment B raw29363step1 raw29363step1Labels := by
      have ha : raw29363step1 = (fun i j => raw29363step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29363step1 raw29363step0; decide +kernel
      have hl : raw29363step1Labels = raw29363step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29363step0 raw29363step0Labels permutation151 permutation2
    mixedMoment B raw29363step1 raw29363step1Labels = mixedMoment B raw29363step2 raw29363step2Labels := by
      have ha : raw29363step2 = -raw29363step1 := by apply Matrix.ext; change ∀ i j, raw29363step2 i j = -(raw29363step1 i j); unfold raw29363step2 raw29363step1; decide +kernel
      have hl : raw29363step2Labels = raw29363step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3772 node3772Labels := by rfl

def raw29364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw29364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw29364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29364step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29364step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29364 raw29364Labels = mixedMoment B node3772 node3772Labels := by
  calc
    mixedMoment B raw29364 raw29364Labels = mixedMoment B raw29364step0 raw29364step0Labels := by
      have hz : ∀ j, raw29364 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29364step0 = (fun i j => raw29364 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29364step0 raw29364; decide +kernel
      have hl : raw29364step0Labels = raw29364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29364 raw29364Labels permutation346 hz
    mixedMoment B raw29364step0 raw29364step0Labels = mixedMoment B raw29364step1 raw29364step1Labels := by
      have ha : raw29364step1 = (fun i j => raw29364step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29364step1 raw29364step0; decide +kernel
      have hl : raw29364step1Labels = raw29364step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29364step0 raw29364step0Labels permutation127 permutation2
    mixedMoment B raw29364step1 raw29364step1Labels = mixedMoment B raw29364step2 raw29364step2Labels := by
      have ha : raw29364step2 = -raw29364step1 := by apply Matrix.ext; change ∀ i j, raw29364step2 i j = -(raw29364step1 i j); unfold raw29364step2 raw29364step1; decide +kernel
      have hl : raw29364step2Labels = raw29364step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3772 node3772Labels := by rfl

def raw29365 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![0, 0], ![-2, 2], ![2, -2], ![2, -2]]
def raw29365Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29365step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw29365step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29365step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw29365step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29365 raw29365Labels = mixedMoment B node4089 node4089Labels := by
  calc
    mixedMoment B raw29365 raw29365Labels = mixedMoment B raw29365step0 raw29365step0Labels := by
      have hz : ∀ j, raw29365 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29365step0 = (fun i j => raw29365 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29365step0 raw29365; decide +kernel
      have hl : raw29365step0Labels = raw29365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29365 raw29365Labels permutation346 hz
    mixedMoment B raw29365step0 raw29365step0Labels = mixedMoment B raw29365step1 raw29365step1Labels := by
      have hz : ∀ j, raw29365step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw29365step1 = (fun i j => raw29365step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw29365step1 raw29365step0; decide +kernel
      have hl : raw29365step1Labels = raw29365step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29365step0 raw29365step0Labels permutation32 hz
    _ = mixedMoment B node4089 node4089Labels := by rfl

def raw29366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29366step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29366step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, 0, -2], ![2, -1, -1]]
def raw29366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29366step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29366step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29366 raw29366Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw29366 raw29366Labels = mixedMoment B raw29366step0 raw29366step0Labels := by
      have hz : ∀ j, raw29366 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29366step0 = (fun i j => raw29366 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29366step0 raw29366; decide +kernel
      have hl : raw29366step0Labels = raw29366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29366 raw29366Labels permutation434 hz
    mixedMoment B raw29366step0 raw29366step0Labels = mixedMoment B raw29366step1 raw29366step1Labels := by
      have hz : ∀ j, raw29366step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29366step1 = (fun i j => raw29366step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29366step1 raw29366step0; decide +kernel
      have hl : raw29366step1Labels = raw29366step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29366step0 raw29366step0Labels permutation80 hz
    mixedMoment B raw29366step1 raw29366step1Labels = mixedMoment B raw29366step2 raw29366step2Labels := by
      have ha : raw29366step2 = (fun i j => raw29366step1 (permutation15 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29366step2 raw29366step1; decide +kernel
      have hl : raw29366step2Labels = raw29366step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29366step1 raw29366step1Labels permutation15 permutation2
    _ = mixedMoment B node3397 node3397Labels := by rfl

def raw29367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29367step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, 0, -2], ![2, -1, -1]]
def raw29367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29367step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![2, -1, -1], ![2, 0, -2]]
def raw29367step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29367 raw29367Labels = mixedMoment B node3161 node3161Labels := by
  calc
    mixedMoment B raw29367 raw29367Labels = mixedMoment B raw29367step0 raw29367step0Labels := by
      have hz : ∀ j, raw29367 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29367step0 = (fun i j => raw29367 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29367step0 raw29367; decide +kernel
      have hl : raw29367step0Labels = raw29367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29367 raw29367Labels permutation434 hz
    mixedMoment B raw29367step0 raw29367step0Labels = mixedMoment B raw29367step1 raw29367step1Labels := by
      have hz : ∀ j, raw29367step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29367step1 = (fun i j => raw29367step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29367step1 raw29367step0; decide +kernel
      have hl : raw29367step1Labels = raw29367step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29367step0 raw29367step0Labels permutation80 hz
    mixedMoment B raw29367step1 raw29367step1Labels = mixedMoment B raw29367step2 raw29367step2Labels := by
      have ha : raw29367step2 = (fun i j => raw29367step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29367step2 raw29367step1; decide +kernel
      have hl : raw29367step2Labels = raw29367step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29367step1 raw29367step1Labels permutation9 permutation2
    _ = mixedMoment B node3161 node3161Labels := by rfl

def raw29368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29368 raw29368Labels = mixedMoment B node3129 node3129Labels := by
  calc
    mixedMoment B raw29368 raw29368Labels = mixedMoment B raw29368step0 raw29368step0Labels := by
      have hz : ∀ j, raw29368 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29368step0 = (fun i j => raw29368 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29368step0 raw29368; decide +kernel
      have hl : raw29368step0Labels = raw29368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29368 raw29368Labels permutation434 hz
    mixedMoment B raw29368step0 raw29368step0Labels = mixedMoment B raw29368step1 raw29368step1Labels := by
      have ha : raw29368step1 = (fun i j => raw29368step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29368step1 raw29368step0; decide +kernel
      have hl : raw29368step1Labels = raw29368step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29368step0 raw29368step0Labels permutation33 permutation2
    _ = mixedMoment B node3129 node3129Labels := by rfl

def raw29369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw29369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29369 raw29369Labels = mixedMoment B node3129 node3129Labels := by
  calc
    mixedMoment B raw29369 raw29369Labels = mixedMoment B raw29369step0 raw29369step0Labels := by
      have hz : ∀ j, raw29369 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29369step0 = (fun i j => raw29369 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29369step0 raw29369; decide +kernel
      have hl : raw29369step0Labels = raw29369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29369 raw29369Labels permutation346 hz
    mixedMoment B raw29369step0 raw29369step0Labels = mixedMoment B raw29369step1 raw29369step1Labels := by
      have ha : raw29369step1 = (fun i j => raw29369step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29369step1 raw29369step0; decide +kernel
      have hl : raw29369step1Labels = raw29369step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29369step0 raw29369step0Labels permutation33 permutation2
    _ = mixedMoment B node3129 node3129Labels := by rfl

def raw29370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw29370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29370step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![3, -1, -2], ![2, -1, -1]]
def raw29370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29370step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-2, -1, 3], ![-3, 3, 0]]
def raw29370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29370step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 1, -3], ![3, -3, 0]]
def raw29370step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29370 raw29370Labels = mixedMoment B node2346 node2346Labels := by
  calc
    mixedMoment B raw29370 raw29370Labels = mixedMoment B raw29370step0 raw29370step0Labels := by
      have hz : ∀ j, raw29370 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29370step0 = (fun i j => raw29370 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29370step0 raw29370; decide +kernel
      have hl : raw29370step0Labels = raw29370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29370 raw29370Labels permutation434 hz
    mixedMoment B raw29370step0 raw29370step0Labels = mixedMoment B raw29370step1 raw29370step1Labels := by
      have hz : ∀ j, raw29370step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29370step1 = (fun i j => raw29370step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29370step1 raw29370step0; decide +kernel
      have hl : raw29370step1Labels = raw29370step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29370step0 raw29370step0Labels permutation80 hz
    mixedMoment B raw29370step1 raw29370step1Labels = mixedMoment B raw29370step2 raw29370step2Labels := by
      have ha : raw29370step2 = (fun i j => raw29370step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29370step2 raw29370step1; decide +kernel
      have hl : raw29370step2Labels = raw29370step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29370step1 raw29370step1Labels permutation25 permutation2
    mixedMoment B raw29370step2 raw29370step2Labels = mixedMoment B raw29370step3 raw29370step3Labels := by
      have ha : raw29370step3 = -raw29370step2 := by apply Matrix.ext; change ∀ i j, raw29370step3 i j = -(raw29370step2 i j); unfold raw29370step3 raw29370step2; decide +kernel
      have hl : raw29370step3Labels = raw29370step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2346 node2346Labels := by rfl

def raw29371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw29371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29371step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, 0, -2], ![3, -2, -1]]
def raw29371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29371step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-2, -1, 3], ![-3, 3, 0]]
def raw29371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29371step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![2, 1, -3], ![3, -3, 0]]
def raw29371step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29371 raw29371Labels = mixedMoment B node2821 node2821Labels := by
  calc
    mixedMoment B raw29371 raw29371Labels = mixedMoment B raw29371step0 raw29371step0Labels := by
      have hz : ∀ j, raw29371 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29371step0 = (fun i j => raw29371 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29371step0 raw29371; decide +kernel
      have hl : raw29371step0Labels = raw29371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29371 raw29371Labels permutation434 hz
    mixedMoment B raw29371step0 raw29371step0Labels = mixedMoment B raw29371step1 raw29371step1Labels := by
      have hz : ∀ j, raw29371step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29371step1 = (fun i j => raw29371step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29371step1 raw29371step0; decide +kernel
      have hl : raw29371step1Labels = raw29371step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29371step0 raw29371step0Labels permutation80 hz
    mixedMoment B raw29371step1 raw29371step1Labels = mixedMoment B raw29371step2 raw29371step2Labels := by
      have ha : raw29371step2 = (fun i j => raw29371step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29371step2 raw29371step1; decide +kernel
      have hl : raw29371step2Labels = raw29371step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29371step1 raw29371step1Labels permutation31 permutation2
    mixedMoment B raw29371step2 raw29371step2Labels = mixedMoment B raw29371step3 raw29371step3Labels := by
      have ha : raw29371step3 = -raw29371step2 := by apply Matrix.ext; change ∀ i j, raw29371step3 i j = -(raw29371step2 i j); unfold raw29371step3 raw29371step2; decide +kernel
      have hl : raw29371step3Labels = raw29371step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2821 node2821Labels := by rfl

def raw29372 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![0, 0], ![2, -2], ![1, -1]]
def raw29372Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29372step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![2, -2], ![1, -1]]
def raw29372step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29372step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![2, -2], ![1, -1]]
def raw29372step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29372step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw29372step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29372step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw29372step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29372 raw29372Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw29372 raw29372Labels = mixedMoment B raw29372step0 raw29372step0Labels := by
      have hz : ∀ j, raw29372 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29372step0 = (fun i j => raw29372 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29372step0 raw29372; decide +kernel
      have hl : raw29372step0Labels = raw29372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29372 raw29372Labels permutation434 hz
    mixedMoment B raw29372step0 raw29372step0Labels = mixedMoment B raw29372step1 raw29372step1Labels := by
      have hz : ∀ j, raw29372step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29372step1 = (fun i j => raw29372step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29372step1 raw29372step0; decide +kernel
      have hl : raw29372step1Labels = raw29372step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29372step0 raw29372step0Labels permutation80 hz
    mixedMoment B raw29372step1 raw29372step1Labels = mixedMoment B raw29372step2 raw29372step2Labels := by
      have hz : ∀ j, raw29372step1 (permutation8 0) j = 0 := by decide +kernel
      have ha : raw29372step2 = (fun i j => raw29372step1 (permutation8 i.succ) j) := by apply Matrix.ext; unfold raw29372step2 raw29372step1; decide +kernel
      have hl : raw29372step2Labels = raw29372step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29372step1 raw29372step1Labels permutation8 hz
    mixedMoment B raw29372step2 raw29372step2Labels = mixedMoment B raw29372step3 raw29372step3Labels := by
      have ha : raw29372step3 = (fun i j => raw29372step2 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29372step3 raw29372step2; decide +kernel
      have hl : raw29372step3Labels = raw29372step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29372step2 raw29372step2Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw29373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29373 raw29373Labels = mixedMoment B node3147 node3147Labels := by
  calc
    mixedMoment B raw29373 raw29373Labels = mixedMoment B raw29373step0 raw29373step0Labels := by
      have hz : ∀ j, raw29373 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29373step0 = (fun i j => raw29373 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29373step0 raw29373; decide +kernel
      have hl : raw29373step0Labels = raw29373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29373 raw29373Labels permutation346 hz
    _ = mixedMoment B node3147 node3147Labels := by rfl

def raw29374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29374 raw29374Labels = mixedMoment B node3372 node3372Labels := by
  calc
    mixedMoment B raw29374 raw29374Labels = mixedMoment B raw29374step0 raw29374step0Labels := by
      have hz : ∀ j, raw29374 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29374step0 = (fun i j => raw29374 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29374step0 raw29374; decide +kernel
      have hl : raw29374step0Labels = raw29374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29374 raw29374Labels permutation346 hz
    mixedMoment B raw29374step0 raw29374step0Labels = mixedMoment B raw29374step1 raw29374step1Labels := by
      have ha : raw29374step1 = (fun i j => raw29374step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29374step1 raw29374step0; decide +kernel
      have hl : raw29374step1Labels = raw29374step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29374step0 raw29374step0Labels permutation56 permutation2
    _ = mixedMoment B node3372 node3372Labels := by rfl

def raw29375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw29375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29375 raw29375Labels = mixedMoment B node3473 node3473Labels := by
  calc
    mixedMoment B raw29375 raw29375Labels = mixedMoment B raw29375step0 raw29375step0Labels := by
      have ha : raw29375step0 = (fun i j => raw29375 (permutation317 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29375step0 raw29375; decide +kernel
      have hl : raw29375step0Labels = raw29375Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29375 raw29375Labels permutation317 permutation4
    _ = mixedMoment B node3473 node3473Labels := by rfl

def raw29376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29376Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29376step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]
def raw29376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29376 raw29376Labels = mixedMoment B node3611 node3611Labels := by
  calc
    mixedMoment B raw29376 raw29376Labels = mixedMoment B raw29376step0 raw29376step0Labels := by
      have hz : ∀ j, raw29376 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29376step0 = (fun i j => raw29376 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29376step0 raw29376; decide +kernel
      have hl : raw29376step0Labels = raw29376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29376 raw29376Labels permutation346 hz
    mixedMoment B raw29376step0 raw29376step0Labels = mixedMoment B raw29376step1 raw29376step1Labels := by
      have ha : raw29376step1 = (fun i j => raw29376step0 (permutation65 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29376step1 raw29376step0; decide +kernel
      have hl : raw29376step1Labels = raw29376step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29376step0 raw29376step0Labels permutation65 permutation4
    _ = mixedMoment B node3611 node3611Labels := by rfl

def raw29377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29377 raw29377Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw29377 raw29377Labels = mixedMoment B raw29377step0 raw29377step0Labels := by
      have hz : ∀ j, raw29377 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29377step0 = (fun i j => raw29377 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29377step0 raw29377; decide +kernel
      have hl : raw29377step0Labels = raw29377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29377 raw29377Labels permutation346 hz
    mixedMoment B raw29377step0 raw29377step0Labels = mixedMoment B raw29377step1 raw29377step1Labels := by
      have ha : raw29377step1 = (fun i j => raw29377step0 (permutation67 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29377step1 raw29377step0; decide +kernel
      have hl : raw29377step1Labels = raw29377step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29377step0 raw29377step0Labels permutation67 permutation4
    _ = mixedMoment B node3480 node3480Labels := by rfl

def raw29378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw29378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw29378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29378 raw29378Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw29378 raw29378Labels = mixedMoment B raw29378step0 raw29378step0Labels := by
      have hz : ∀ j, raw29378 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29378step0 = (fun i j => raw29378 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29378step0 raw29378; decide +kernel
      have hl : raw29378step0Labels = raw29378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29378 raw29378Labels permutation346 hz
    mixedMoment B raw29378step0 raw29378step0Labels = mixedMoment B raw29378step1 raw29378step1Labels := by
      have ha : raw29378step1 = (fun i j => raw29378step0 (permutation65 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29378step1 raw29378step0; decide +kernel
      have hl : raw29378step1Labels = raw29378step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29378step0 raw29378step0Labels permutation65 permutation4
    _ = mixedMoment B node3480 node3480Labels := by rfl

def raw29379 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![2, -2]]
def raw29379Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29379step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw29379step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29379step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw29379step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29379 raw29379Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw29379 raw29379Labels = mixedMoment B raw29379step0 raw29379step0Labels := by
      have hz : ∀ j, raw29379 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29379step0 = (fun i j => raw29379 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29379step0 raw29379; decide +kernel
      have hl : raw29379step0Labels = raw29379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29379 raw29379Labels permutation346 hz
    mixedMoment B raw29379step0 raw29379step0Labels = mixedMoment B raw29379step1 raw29379step1Labels := by
      have hz : ∀ j, raw29379step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw29379step1 = (fun i j => raw29379step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw29379step1 raw29379step0; decide +kernel
      have hl : raw29379step1Labels = raw29379step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29379step0 raw29379step0Labels permutation32 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw29380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29380Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29380 raw29380Labels = mixedMoment B node1141 node1141Labels := by
  calc
    mixedMoment B raw29380 raw29380Labels = mixedMoment B raw29380step0 raw29380step0Labels := by
      have hz : ∀ j, raw29380 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29380step0 = (fun i j => raw29380 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29380step0 raw29380; decide +kernel
      have hl : raw29380step0Labels = raw29380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29380 raw29380Labels permutation346 hz
    _ = mixedMoment B node1141 node1141Labels := by rfl

def raw29381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29381 raw29381Labels = mixedMoment B node2343 node2343Labels := by
  calc
    mixedMoment B raw29381 raw29381Labels = mixedMoment B raw29381step0 raw29381step0Labels := by
      have hz : ∀ j, raw29381 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29381step0 = (fun i j => raw29381 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29381step0 raw29381; decide +kernel
      have hl : raw29381step0Labels = raw29381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29381 raw29381Labels permutation346 hz
    _ = mixedMoment B node2343 node2343Labels := by rfl

def raw29382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29382Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29382 raw29382Labels = mixedMoment B node2433 node2433Labels := by
  calc
    _ = mixedMoment B node2433 node2433Labels := by rfl

def raw29383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw29383Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw29383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw29383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29383 raw29383Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw29383 raw29383Labels = mixedMoment B raw29383step0 raw29383step0Labels := by
      have hz : ∀ j, raw29383 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29383step0 = (fun i j => raw29383 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29383step0 raw29383; decide +kernel
      have hl : raw29383step0Labels = raw29383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29383 raw29383Labels permutation346 hz
    mixedMoment B raw29383step0 raw29383step0Labels = mixedMoment B raw29383step1 raw29383step1Labels := by
      have ha : raw29383step1 = (fun i j => raw29383step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29383step1 raw29383step0; decide +kernel
      have hl : raw29383step1Labels = raw29383step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29383step0 raw29383step0Labels permutation36 permutation2
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw29384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29384Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29384step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw29384step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29384step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw29384step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29384 raw29384Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw29384 raw29384Labels = mixedMoment B raw29384step0 raw29384step0Labels := by
      have hz : ∀ j, raw29384 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29384step0 = (fun i j => raw29384 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29384step0 raw29384; decide +kernel
      have hl : raw29384step0Labels = raw29384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29384 raw29384Labels permutation346 hz
    mixedMoment B raw29384step0 raw29384step0Labels = mixedMoment B raw29384step1 raw29384step1Labels := by
      have ha : raw29384step1 = (fun i j => raw29384step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29384step1 raw29384step0; decide +kernel
      have hl : raw29384step1Labels = raw29384step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29384step0 raw29384step0Labels permutation125 permutation2
    mixedMoment B raw29384step1 raw29384step1Labels = mixedMoment B raw29384step2 raw29384step2Labels := by
      have ha : raw29384step2 = -raw29384step1 := by apply Matrix.ext; change ∀ i j, raw29384step2 i j = -(raw29384step1 i j); unfold raw29384step2 raw29384step1; decide +kernel
      have hl : raw29384step2Labels = raw29384step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3705 node3705Labels := by rfl

def raw29385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29385Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29385step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29385 raw29385Labels = mixedMoment B node2846 node2846Labels := by
  calc
    mixedMoment B raw29385 raw29385Labels = mixedMoment B raw29385step0 raw29385step0Labels := by
      have ha : raw29385step0 = (fun i j => raw29385 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29385step0 raw29385; decide +kernel
      have hl : raw29385step0Labels = raw29385Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29385 raw29385Labels permutation201 permutation2
    _ = mixedMoment B node2846 node2846Labels := by rfl

def raw29386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw29386Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw29386step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw29386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29386step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw29386step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29386 raw29386Labels = mixedMoment B node2335 node2335Labels := by
  calc
    mixedMoment B raw29386 raw29386Labels = mixedMoment B raw29386step0 raw29386step0Labels := by
      have hz : ∀ j, raw29386 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29386step0 = (fun i j => raw29386 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29386step0 raw29386; decide +kernel
      have hl : raw29386step0Labels = raw29386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29386 raw29386Labels permutation346 hz
    mixedMoment B raw29386step0 raw29386step0Labels = mixedMoment B raw29386step1 raw29386step1Labels := by
      have ha : raw29386step1 = (fun i j => raw29386step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29386step1 raw29386step0; decide +kernel
      have hl : raw29386step1Labels = raw29386step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29386step0 raw29386step0Labels permutation125 permutation2
    mixedMoment B raw29386step1 raw29386step1Labels = mixedMoment B raw29386step2 raw29386step2Labels := by
      have ha : raw29386step2 = -raw29386step1 := by apply Matrix.ext; change ∀ i j, raw29386step2 i j = -(raw29386step1 i j); unfold raw29386step2 raw29386step1; decide +kernel
      have hl : raw29386step2Labels = raw29386step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2335 node2335Labels := by rfl

def raw29387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw29387Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw29387step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw29387step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29387step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw29387step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29387 raw29387Labels = mixedMoment B node2811 node2811Labels := by
  calc
    mixedMoment B raw29387 raw29387Labels = mixedMoment B raw29387step0 raw29387step0Labels := by
      have hz : ∀ j, raw29387 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29387step0 = (fun i j => raw29387 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29387step0 raw29387; decide +kernel
      have hl : raw29387step0Labels = raw29387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29387 raw29387Labels permutation346 hz
    mixedMoment B raw29387step0 raw29387step0Labels = mixedMoment B raw29387step1 raw29387step1Labels := by
      have ha : raw29387step1 = (fun i j => raw29387step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29387step1 raw29387step0; decide +kernel
      have hl : raw29387step1Labels = raw29387step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29387step0 raw29387step0Labels permutation149 permutation2
    mixedMoment B raw29387step1 raw29387step1Labels = mixedMoment B raw29387step2 raw29387step2Labels := by
      have ha : raw29387step2 = -raw29387step1 := by apply Matrix.ext; change ∀ i j, raw29387step2 i j = -(raw29387step1 i j); unfold raw29387step2 raw29387step1; decide +kernel
      have hl : raw29387step2Labels = raw29387step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2811 node2811Labels := by rfl

def raw29388 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29388Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29388step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29388step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29388step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29388step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29388 raw29388Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw29388 raw29388Labels = mixedMoment B raw29388step0 raw29388step0Labels := by
      have hz : ∀ j, raw29388 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29388step0 = (fun i j => raw29388 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29388step0 raw29388; decide +kernel
      have hl : raw29388step0Labels = raw29388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29388 raw29388Labels permutation346 hz
    mixedMoment B raw29388step0 raw29388step0Labels = mixedMoment B raw29388step1 raw29388step1Labels := by
      have ha : raw29388step1 = (fun i j => raw29388step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29388step1 raw29388step0; decide +kernel
      have hl : raw29388step1Labels = raw29388step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29388step0 raw29388step0Labels permutation35 permutation4
    mixedMoment B raw29388step1 raw29388step1Labels = mixedMoment B raw29388step2 raw29388step2Labels := by
      have ha : raw29388step2 = -raw29388step1 := by apply Matrix.ext; change ∀ i j, raw29388step2 i j = -(raw29388step1 i j); unfold raw29388step2 raw29388step1; decide +kernel
      have hl : raw29388step2Labels = raw29388step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3480 node3480Labels := by rfl

def raw29389 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29389Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29389step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29389step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29389step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29389step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29389 raw29389Labels = mixedMoment B node3386 node3386Labels := by
  calc
    mixedMoment B raw29389 raw29389Labels = mixedMoment B raw29389step0 raw29389step0Labels := by
      have hz : ∀ j, raw29389 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29389step0 = (fun i j => raw29389 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29389step0 raw29389; decide +kernel
      have hl : raw29389step0Labels = raw29389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29389 raw29389Labels permutation346 hz
    mixedMoment B raw29389step0 raw29389step0Labels = mixedMoment B raw29389step1 raw29389step1Labels := by
      have ha : raw29389step1 = (fun i j => raw29389step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29389step1 raw29389step0; decide +kernel
      have hl : raw29389step1Labels = raw29389step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29389step0 raw29389step0Labels permutation39 permutation2
    mixedMoment B raw29389step1 raw29389step1Labels = mixedMoment B raw29389step2 raw29389step2Labels := by
      have ha : raw29389step2 = -raw29389step1 := by apply Matrix.ext; change ∀ i j, raw29389step2 i j = -(raw29389step1 i j); unfold raw29389step2 raw29389step1; decide +kernel
      have hl : raw29389step2Labels = raw29389step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3386 node3386Labels := by rfl

def raw29390 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29390Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29390step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29390step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw29390step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29390 raw29390Labels = mixedMoment B node3369 node3369Labels := by
  calc
    mixedMoment B raw29390 raw29390Labels = mixedMoment B raw29390step0 raw29390step0Labels := by
      have ha : raw29390step0 = (fun i j => raw29390 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29390step0 raw29390; decide +kernel
      have hl : raw29390step0Labels = raw29390Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29390 raw29390Labels permutation201 permutation2
    mixedMoment B raw29390step0 raw29390step0Labels = mixedMoment B raw29390step1 raw29390step1Labels := by
      have ha : raw29390step1 = -raw29390step0 := by apply Matrix.ext; change ∀ i j, raw29390step1 i j = -(raw29390step0 i j); unfold raw29390step1 raw29390step0; decide +kernel
      have hl : raw29390step1Labels = raw29390step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3369 node3369Labels := by rfl

def raw29391 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29391Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29391step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29391step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29391step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29391step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29391 raw29391Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw29391 raw29391Labels = mixedMoment B raw29391step0 raw29391step0Labels := by
      have hz : ∀ j, raw29391 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29391step0 = (fun i j => raw29391 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29391step0 raw29391; decide +kernel
      have hl : raw29391step0Labels = raw29391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29391 raw29391Labels permutation346 hz
    mixedMoment B raw29391step0 raw29391step0Labels = mixedMoment B raw29391step1 raw29391step1Labels := by
      have ha : raw29391step1 = (fun i j => raw29391step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29391step1 raw29391step0; decide +kernel
      have hl : raw29391step1Labels = raw29391step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29391step0 raw29391step0Labels permutation39 permutation2
    mixedMoment B raw29391step1 raw29391step1Labels = mixedMoment B raw29391step2 raw29391step2Labels := by
      have ha : raw29391step2 = -raw29391step1 := by apply Matrix.ext; change ∀ i j, raw29391step2 i j = -(raw29391step1 i j); unfold raw29391step2 raw29391step1; decide +kernel
      have hl : raw29391step2Labels = raw29391step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3522 node3522Labels := by rfl

def raw29392 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29392Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![2, -2, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29392step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29392step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw29392step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29392 raw29392Labels = mixedMoment B node2387 node2387Labels := by
  calc
    mixedMoment B raw29392 raw29392Labels = mixedMoment B raw29392step0 raw29392step0Labels := by
      have hz : ∀ j, raw29392 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29392step0 = (fun i j => raw29392 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29392step0 raw29392; decide +kernel
      have hl : raw29392step0Labels = raw29392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29392 raw29392Labels permutation346 hz
    mixedMoment B raw29392step0 raw29392step0Labels = mixedMoment B raw29392step1 raw29392step1Labels := by
      have ha : raw29392step1 = (fun i j => raw29392step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29392step1 raw29392step0; decide +kernel
      have hl : raw29392step1Labels = raw29392step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29392step0 raw29392step0Labels permutation125 permutation2
    _ = mixedMoment B node2387 node2387Labels := by rfl

def raw29393 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29393Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29393step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw29393step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29393step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29393step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29393 raw29393Labels = mixedMoment B node3372 node3372Labels := by
  calc
    mixedMoment B raw29393 raw29393Labels = mixedMoment B raw29393step0 raw29393step0Labels := by
      have hz : ∀ j, raw29393 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29393step0 = (fun i j => raw29393 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29393step0 raw29393; decide +kernel
      have hl : raw29393step0Labels = raw29393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29393 raw29393Labels permutation346 hz
    mixedMoment B raw29393step0 raw29393step0Labels = mixedMoment B raw29393step1 raw29393step1Labels := by
      have ha : raw29393step1 = (fun i j => raw29393step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29393step1 raw29393step0; decide +kernel
      have hl : raw29393step1Labels = raw29393step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29393step0 raw29393step0Labels permutation38 permutation2
    mixedMoment B raw29393step1 raw29393step1Labels = mixedMoment B raw29393step2 raw29393step2Labels := by
      have ha : raw29393step2 = -raw29393step1 := by apply Matrix.ext; change ∀ i j, raw29393step2 i j = -(raw29393step1 i j); unfold raw29393step2 raw29393step1; decide +kernel
      have hl : raw29393step2Labels = raw29393step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3372 node3372Labels := by rfl

def raw29394 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29394Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29394step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29394step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29394step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29394step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29394 raw29394Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw29394 raw29394Labels = mixedMoment B raw29394step0 raw29394step0Labels := by
      have hz : ∀ j, raw29394 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29394step0 = (fun i j => raw29394 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29394step0 raw29394; decide +kernel
      have hl : raw29394step0Labels = raw29394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29394 raw29394Labels permutation346 hz
    mixedMoment B raw29394step0 raw29394step0Labels = mixedMoment B raw29394step1 raw29394step1Labels := by
      have ha : raw29394step1 = (fun i j => raw29394step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29394step1 raw29394step0; decide +kernel
      have hl : raw29394step1Labels = raw29394step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29394step0 raw29394step0Labels permutation32 permutation4
    mixedMoment B raw29394step1 raw29394step1Labels = mixedMoment B raw29394step2 raw29394step2Labels := by
      have ha : raw29394step2 = -raw29394step1 := by apply Matrix.ext; change ∀ i j, raw29394step2 i j = -(raw29394step1 i j); unfold raw29394step2 raw29394step1; decide +kernel
      have hl : raw29394step2Labels = raw29394step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3482 node3482Labels := by rfl

def raw29395 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29395Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29395step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw29395step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw29395step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29395 raw29395Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw29395 raw29395Labels = mixedMoment B raw29395step0 raw29395step0Labels := by
      have hz : ∀ j, raw29395 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29395step0 = (fun i j => raw29395 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29395step0 raw29395; decide +kernel
      have hl : raw29395step0Labels = raw29395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29395 raw29395Labels permutation346 hz
    mixedMoment B raw29395step0 raw29395step0Labels = mixedMoment B raw29395step1 raw29395step1Labels := by
      have ha : raw29395step1 = (fun i j => raw29395step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29395step1 raw29395step0; decide +kernel
      have hl : raw29395step1Labels = raw29395step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29395step0 raw29395step0Labels permutation34 permutation4
    mixedMoment B raw29395step1 raw29395step1Labels = mixedMoment B raw29395step2 raw29395step2Labels := by
      have ha : raw29395step2 = -raw29395step1 := by apply Matrix.ext; change ∀ i j, raw29395step2 i j = -(raw29395step1 i j); unfold raw29395step2 raw29395step1; decide +kernel
      have hl : raw29395step2Labels = raw29395step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3478 node3478Labels := by rfl

def raw29396 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29396Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29396step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29396step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29396 raw29396Labels = mixedMoment B node1949 node1949Labels := by
  calc
    mixedMoment B raw29396 raw29396Labels = mixedMoment B raw29396step0 raw29396step0Labels := by
      have hz : ∀ j, raw29396 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29396step0 = (fun i j => raw29396 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29396step0 raw29396; decide +kernel
      have hl : raw29396step0Labels = raw29396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29396 raw29396Labels permutation346 hz
    mixedMoment B raw29396step0 raw29396step0Labels = mixedMoment B raw29396step1 raw29396step1Labels := by
      have ha : raw29396step1 = (fun i j => raw29396step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29396step1 raw29396step0; decide +kernel
      have hl : raw29396step1Labels = raw29396step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29396step0 raw29396step0Labels permutation35 permutation4
    mixedMoment B raw29396step1 raw29396step1Labels = mixedMoment B raw29396step2 raw29396step2Labels := by
      have ha : raw29396step2 = -raw29396step1 := by apply Matrix.ext; change ∀ i j, raw29396step2 i j = -(raw29396step1 i j); unfold raw29396step2 raw29396step1; decide +kernel
      have hl : raw29396step2Labels = raw29396step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1949 node1949Labels := by rfl

def raw29397 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29397Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29397step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29397step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29397step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29397 raw29397Labels = mixedMoment B node3359 node3359Labels := by
  calc
    mixedMoment B raw29397 raw29397Labels = mixedMoment B raw29397step0 raw29397step0Labels := by
      have hz : ∀ j, raw29397 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29397step0 = (fun i j => raw29397 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29397step0 raw29397; decide +kernel
      have hl : raw29397step0Labels = raw29397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29397 raw29397Labels permutation346 hz
    mixedMoment B raw29397step0 raw29397step0Labels = mixedMoment B raw29397step1 raw29397step1Labels := by
      have ha : raw29397step1 = (fun i j => raw29397step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29397step1 raw29397step0; decide +kernel
      have hl : raw29397step1Labels = raw29397step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29397step0 raw29397step0Labels permutation35 permutation4
    mixedMoment B raw29397step1 raw29397step1Labels = mixedMoment B raw29397step2 raw29397step2Labels := by
      have ha : raw29397step2 = -raw29397step1 := by apply Matrix.ext; change ∀ i j, raw29397step2 i j = -(raw29397step1 i j); unfold raw29397step2 raw29397step1; decide +kernel
      have hl : raw29397step2Labels = raw29397step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3359 node3359Labels := by rfl

def raw29398 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29398Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29398step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29398 raw29398Labels = mixedMoment B node3438 node3438Labels := by
  calc
    mixedMoment B raw29398 raw29398Labels = mixedMoment B raw29398step0 raw29398step0Labels := by
      have ha : raw29398step0 = (fun i j => raw29398 (permutation155 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29398step0 raw29398; decide +kernel
      have hl : raw29398step0Labels = raw29398Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29398 raw29398Labels permutation155 permutation4
    mixedMoment B raw29398step0 raw29398step0Labels = mixedMoment B raw29398step1 raw29398step1Labels := by
      have ha : raw29398step1 = -raw29398step0 := by apply Matrix.ext; change ∀ i j, raw29398step1 i j = -(raw29398step0 i j); unfold raw29398step1 raw29398step0; decide +kernel
      have hl : raw29398step1Labels = raw29398step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3438 node3438Labels := by rfl

def raw29399 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29399Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29399step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw29399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29399step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw29399step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29399 raw29399Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw29399 raw29399Labels = mixedMoment B raw29399step0 raw29399step0Labels := by
      have hz : ∀ j, raw29399 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29399step0 = (fun i j => raw29399 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29399step0 raw29399; decide +kernel
      have hl : raw29399step0Labels = raw29399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29399 raw29399Labels permutation346 hz
    mixedMoment B raw29399step0 raw29399step0Labels = mixedMoment B raw29399step1 raw29399step1Labels := by
      have ha : raw29399step1 = (fun i j => raw29399step0 (permutation37 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29399step1 raw29399step0; decide +kernel
      have hl : raw29399step1Labels = raw29399step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29399step0 raw29399step0Labels permutation37 permutation4
    mixedMoment B raw29399step1 raw29399step1Labels = mixedMoment B raw29399step2 raw29399step2Labels := by
      have ha : raw29399step2 = -raw29399step1 := by apply Matrix.ext; change ∀ i j, raw29399step2 i j = -(raw29399step1 i j); unfold raw29399step2 raw29399step1; decide +kernel
      have hl : raw29399step2Labels = raw29399step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3480 node3480Labels := by rfl

def raw29400 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29400Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29400step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw29400step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29400step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw29400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29400 raw29400Labels = mixedMoment B node1928 node1928Labels := by
  calc
    mixedMoment B raw29400 raw29400Labels = mixedMoment B raw29400step0 raw29400step0Labels := by
      have hz : ∀ j, raw29400 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29400step0 = (fun i j => raw29400 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29400step0 raw29400; decide +kernel
      have hl : raw29400step0Labels = raw29400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29400 raw29400Labels permutation346 hz
    mixedMoment B raw29400step0 raw29400step0Labels = mixedMoment B raw29400step1 raw29400step1Labels := by
      have ha : raw29400step1 = (fun i j => raw29400step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29400step1 raw29400step0; decide +kernel
      have hl : raw29400step1Labels = raw29400step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29400step0 raw29400step0Labels permutation34 permutation4
    mixedMoment B raw29400step1 raw29400step1Labels = mixedMoment B raw29400step2 raw29400step2Labels := by
      have ha : raw29400step2 = -raw29400step1 := by apply Matrix.ext; change ∀ i j, raw29400step2 i j = -(raw29400step1 i j); unfold raw29400step2 raw29400step1; decide +kernel
      have hl : raw29400step2Labels = raw29400step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1928 node1928Labels := by rfl

def raw29401 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw29401step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29401step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw29401step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29401 raw29401Labels = mixedMoment B node3348 node3348Labels := by
  calc
    mixedMoment B raw29401 raw29401Labels = mixedMoment B raw29401step0 raw29401step0Labels := by
      have hz : ∀ j, raw29401 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29401step0 = (fun i j => raw29401 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29401step0 raw29401; decide +kernel
      have hl : raw29401step0Labels = raw29401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29401 raw29401Labels permutation346 hz
    mixedMoment B raw29401step0 raw29401step0Labels = mixedMoment B raw29401step1 raw29401step1Labels := by
      have ha : raw29401step1 = (fun i j => raw29401step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29401step1 raw29401step0; decide +kernel
      have hl : raw29401step1Labels = raw29401step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29401step0 raw29401step0Labels permutation34 permutation4
    mixedMoment B raw29401step1 raw29401step1Labels = mixedMoment B raw29401step2 raw29401step2Labels := by
      have ha : raw29401step2 = -raw29401step1 := by apply Matrix.ext; change ∀ i j, raw29401step2 i j = -(raw29401step1 i j); unfold raw29401step2 raw29401step1; decide +kernel
      have hl : raw29401step2Labels = raw29401step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3348 node3348Labels := by rfl

def raw29402 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29402Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw29402step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29402step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw29402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29402 raw29402Labels = mixedMoment B node3430 node3430Labels := by
  calc
    mixedMoment B raw29402 raw29402Labels = mixedMoment B raw29402step0 raw29402step0Labels := by
      have ha : raw29402step0 = (fun i j => raw29402 (permutation154 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29402step0 raw29402; decide +kernel
      have hl : raw29402step0Labels = raw29402Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29402 raw29402Labels permutation154 permutation4
    mixedMoment B raw29402step0 raw29402step0Labels = mixedMoment B raw29402step1 raw29402step1Labels := by
      have ha : raw29402step1 = -raw29402step0 := by apply Matrix.ext; change ∀ i j, raw29402step1 i j = -(raw29402step0 i j); unfold raw29402step1 raw29402step0; decide +kernel
      have hl : raw29402step1Labels = raw29402step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3430 node3430Labels := by rfl

def raw29403 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29403Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29403step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw29403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29403 raw29403Labels = mixedMoment B node2674 node2674Labels := by
  calc
    mixedMoment B raw29403 raw29403Labels = mixedMoment B raw29403step0 raw29403step0Labels := by
      have hz : ∀ j, raw29403 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29403step0 = (fun i j => raw29403 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29403step0 raw29403; decide +kernel
      have hl : raw29403step0Labels = raw29403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29403 raw29403Labels permutation346 hz
    mixedMoment B raw29403step0 raw29403step0Labels = mixedMoment B raw29403step1 raw29403step1Labels := by
      have ha : raw29403step1 = (fun i j => raw29403step0 (permutation124 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29403step1 raw29403step0; decide +kernel
      have hl : raw29403step1Labels = raw29403step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29403step0 raw29403step0Labels permutation124 permutation2
    _ = mixedMoment B node2674 node2674Labels := by rfl

def raw29404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29404Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29404step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29404step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29404 raw29404Labels = mixedMoment B node1117 node1117Labels := by
  calc
    mixedMoment B raw29404 raw29404Labels = mixedMoment B raw29404step0 raw29404step0Labels := by
      have ha : raw29404step0 = (fun i j => raw29404 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29404step0 raw29404; decide +kernel
      have hl : raw29404step0Labels = raw29404Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29404 raw29404Labels permutation158 permutation2
    _ = mixedMoment B node1117 node1117Labels := by rfl

def raw29405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29405Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29405 raw29405Labels = mixedMoment B node2324 node2324Labels := by
  calc
    mixedMoment B raw29405 raw29405Labels = mixedMoment B raw29405step0 raw29405step0Labels := by
      have ha : raw29405step0 = (fun i j => raw29405 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29405step0 raw29405; decide +kernel
      have hl : raw29405step0Labels = raw29405Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29405 raw29405Labels permutation158 permutation2
    _ = mixedMoment B node2324 node2324Labels := by rfl

def raw29406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29406Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw29406step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29406 raw29406Labels = mixedMoment B node2441 node2441Labels := by
  calc
    mixedMoment B raw29406 raw29406Labels = mixedMoment B raw29406step0 raw29406step0Labels := by
      have ha : raw29406step0 = (fun i j => raw29406 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29406step0 raw29406; decide +kernel
      have hl : raw29406step0Labels = raw29406Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29406 raw29406Labels permutation158 permutation2
    _ = mixedMoment B node2441 node2441Labels := by rfl

def raw29407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw29407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw29407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29407 raw29407Labels = mixedMoment B node2483 node2483Labels := by
  calc
    mixedMoment B raw29407 raw29407Labels = mixedMoment B raw29407step0 raw29407step0Labels := by
      have ha : raw29407step0 = (fun i j => raw29407 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29407step0 raw29407; decide +kernel
      have hl : raw29407step0Labels = raw29407Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29407 raw29407Labels permutation159 permutation2
    _ = mixedMoment B node2483 node2483Labels := by rfl

def raw29408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29408step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29408 raw29408Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw29408 raw29408Labels = mixedMoment B raw29408step0 raw29408step0Labels := by
      have ha : raw29408step0 = (fun i j => raw29408 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29408step0 raw29408; decide +kernel
      have hl : raw29408step0Labels = raw29408Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29408 raw29408Labels permutation587 permutation2
    mixedMoment B raw29408step0 raw29408step0Labels = mixedMoment B raw29408step1 raw29408step1Labels := by
      have ha : raw29408step1 = -raw29408step0 := by apply Matrix.ext; change ∀ i j, raw29408step1 i j = -(raw29408step0 i j); unfold raw29408step1 raw29408step0; decide +kernel
      have hl : raw29408step1Labels = raw29408step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3690 node3690Labels := by rfl

def raw29409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw29409Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29409 raw29409Labels = mixedMoment B node2900 node2900Labels := by
  calc
    mixedMoment B raw29409 raw29409Labels = mixedMoment B raw29409step0 raw29409step0Labels := by
      have ha : raw29409step0 = (fun i j => raw29409 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29409step0 raw29409; decide +kernel
      have hl : raw29409step0Labels = raw29409Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29409 raw29409Labels permutation177 permutation2
    _ = mixedMoment B node2900 node2900Labels := by rfl

def raw29410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw29410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw29410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29410step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29410 raw29410Labels = mixedMoment B node2320 node2320Labels := by
  calc
    mixedMoment B raw29410 raw29410Labels = mixedMoment B raw29410step0 raw29410step0Labels := by
      have ha : raw29410step0 = (fun i j => raw29410 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29410step0 raw29410; decide +kernel
      have hl : raw29410step0Labels = raw29410Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29410 raw29410Labels permutation587 permutation2
    mixedMoment B raw29410step0 raw29410step0Labels = mixedMoment B raw29410step1 raw29410step1Labels := by
      have ha : raw29410step1 = -raw29410step0 := by apply Matrix.ext; change ∀ i j, raw29410step1 i j = -(raw29410step0 i j); unfold raw29410step1 raw29410step0; decide +kernel
      have hl : raw29410step1Labels = raw29410step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2320 node2320Labels := by rfl

def raw29411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw29411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw29411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29411step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw29411step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29411 raw29411Labels = mixedMoment B node2797 node2797Labels := by
  calc
    mixedMoment B raw29411 raw29411Labels = mixedMoment B raw29411step0 raw29411step0Labels := by
      have ha : raw29411step0 = (fun i j => raw29411 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29411step0 raw29411; decide +kernel
      have hl : raw29411step0Labels = raw29411Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29411 raw29411Labels permutation686 permutation2
    mixedMoment B raw29411step0 raw29411step0Labels = mixedMoment B raw29411step1 raw29411step1Labels := by
      have ha : raw29411step1 = -raw29411step0 := by apply Matrix.ext; change ∀ i j, raw29411step1 i j = -(raw29411step0 i j); unfold raw29411step1 raw29411step0; decide +kernel
      have hl : raw29411step1Labels = raw29411step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2797 node2797Labels := by rfl

def raw29412 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29412Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29412step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29412step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29412 raw29412Labels = mixedMoment B node3491 node3491Labels := by
  calc
    mixedMoment B raw29412 raw29412Labels = mixedMoment B raw29412step0 raw29412step0Labels := by
      have ha : raw29412step0 = (fun i j => raw29412 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29412step0 raw29412; decide +kernel
      have hl : raw29412step0Labels = raw29412Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29412 raw29412Labels permutation183 permutation2
    mixedMoment B raw29412step0 raw29412step0Labels = mixedMoment B raw29412step1 raw29412step1Labels := by
      have ha : raw29412step1 = -raw29412step0 := by apply Matrix.ext; change ∀ i j, raw29412step1 i j = -(raw29412step0 i j); unfold raw29412step1 raw29412step0; decide +kernel
      have hl : raw29412step1Labels = raw29412step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3491 node3491Labels := by rfl

def raw29413 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw29413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29413step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29413step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29413 raw29413Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw29413 raw29413Labels = mixedMoment B raw29413step0 raw29413step0Labels := by
      have hz : ∀ j, raw29413 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29413step0 = (fun i j => raw29413 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29413step0 raw29413; decide +kernel
      have hl : raw29413step0Labels = raw29413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29413 raw29413Labels permutation434 hz
    mixedMoment B raw29413step0 raw29413step0Labels = mixedMoment B raw29413step1 raw29413step1Labels := by
      have ha : raw29413step1 = (fun i j => raw29413step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29413step1 raw29413step0; decide +kernel
      have hl : raw29413step1Labels = raw29413step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29413step0 raw29413step0Labels permutation39 permutation2
    mixedMoment B raw29413step1 raw29413step1Labels = mixedMoment B raw29413step2 raw29413step2Labels := by
      have ha : raw29413step2 = -raw29413step1 := by apply Matrix.ext; change ∀ i j, raw29413step2 i j = -(raw29413step1 i j); unfold raw29413step2 raw29413step1; decide +kernel
      have hl : raw29413step2Labels = raw29413step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3522 node3522Labels := by rfl

def raw29414 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw29414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29414 raw29414Labels = mixedMoment B node2381 node2381Labels := by
  calc
    mixedMoment B raw29414 raw29414Labels = mixedMoment B raw29414step0 raw29414step0Labels := by
      have ha : raw29414step0 = (fun i j => raw29414 (permutation577 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29414step0 raw29414; decide +kernel
      have hl : raw29414step0Labels = raw29414Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29414 raw29414Labels permutation577 permutation2
    _ = mixedMoment B node2381 node2381Labels := by rfl

def raw29415 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29415Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw29415step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29415step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29415 raw29415Labels = mixedMoment B node3487 node3487Labels := by
  calc
    mixedMoment B raw29415 raw29415Labels = mixedMoment B raw29415step0 raw29415step0Labels := by
      have ha : raw29415step0 = (fun i j => raw29415 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29415step0 raw29415; decide +kernel
      have hl : raw29415step0Labels = raw29415Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29415 raw29415Labels permutation182 permutation2
    mixedMoment B raw29415step0 raw29415step0Labels = mixedMoment B raw29415step1 raw29415step1Labels := by
      have ha : raw29415step1 = -raw29415step0 := by apply Matrix.ext; change ∀ i j, raw29415step1 i j = -(raw29415step0 i j); unfold raw29415step1 raw29415step0; decide +kernel
      have hl : raw29415step1Labels = raw29415step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3487 node3487Labels := by rfl

def raw29416 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29416Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29416step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29416 raw29416Labels = mixedMoment B node1941 node1941Labels := by
  calc
    mixedMoment B raw29416 raw29416Labels = mixedMoment B raw29416step0 raw29416step0Labels := by
      have ha : raw29416step0 = (fun i j => raw29416 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29416step0 raw29416; decide +kernel
      have hl : raw29416step0Labels = raw29416Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29416 raw29416Labels permutation152 permutation4
    mixedMoment B raw29416step0 raw29416step0Labels = mixedMoment B raw29416step1 raw29416step1Labels := by
      have ha : raw29416step1 = -raw29416step0 := by apply Matrix.ext; change ∀ i j, raw29416step1 i j = -(raw29416step0 i j); unfold raw29416step1 raw29416step0; decide +kernel
      have hl : raw29416step1Labels = raw29416step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1941 node1941Labels := by rfl

def raw29417 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29417step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29417 raw29417Labels = mixedMoment B node3351 node3351Labels := by
  calc
    mixedMoment B raw29417 raw29417Labels = mixedMoment B raw29417step0 raw29417step0Labels := by
      have ha : raw29417step0 = (fun i j => raw29417 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29417step0 raw29417; decide +kernel
      have hl : raw29417step0Labels = raw29417Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29417 raw29417Labels permutation152 permutation4
    mixedMoment B raw29417step0 raw29417step0Labels = mixedMoment B raw29417step1 raw29417step1Labels := by
      have ha : raw29417step1 = -raw29417step0 := by apply Matrix.ext; change ∀ i j, raw29417step1 i j = -(raw29417step0 i j); unfold raw29417step1 raw29417step0; decide +kernel
      have hl : raw29417step1Labels = raw29417step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3351 node3351Labels := by rfl

def raw29418 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29418Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw29418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29418step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw29418step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29418 raw29418Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw29418 raw29418Labels = mixedMoment B raw29418step0 raw29418step0Labels := by
      have hz : ∀ j, raw29418 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29418step0 = (fun i j => raw29418 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29418step0 raw29418; decide +kernel
      have hl : raw29418step0Labels = raw29418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29418 raw29418Labels permutation434 hz
    mixedMoment B raw29418step0 raw29418step0Labels = mixedMoment B raw29418step1 raw29418step1Labels := by
      have ha : raw29418step1 = (fun i j => raw29418step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29418step1 raw29418step0; decide +kernel
      have hl : raw29418step1Labels = raw29418step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29418step0 raw29418step0Labels permutation32 permutation4
    mixedMoment B raw29418step1 raw29418step1Labels = mixedMoment B raw29418step2 raw29418step2Labels := by
      have ha : raw29418step2 = -raw29418step1 := by apply Matrix.ext; change ∀ i j, raw29418step2 i j = -(raw29418step1 i j); unfold raw29418step2 raw29418step1; decide +kernel
      have hl : raw29418step2Labels = raw29418step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3482 node3482Labels := by rfl

def raw29419 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw29419Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw29419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw29419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29419 raw29419Labels = mixedMoment B node3476 node3476Labels := by
  calc
    mixedMoment B raw29419 raw29419Labels = mixedMoment B raw29419step0 raw29419step0Labels := by
      have ha : raw29419step0 = (fun i j => raw29419 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29419step0 raw29419; decide +kernel
      have hl : raw29419step0Labels = raw29419Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29419 raw29419Labels permutation170 permutation4
    mixedMoment B raw29419step0 raw29419step0Labels = mixedMoment B raw29419step1 raw29419step1Labels := by
      have ha : raw29419step1 = -raw29419step0 := by apply Matrix.ext; change ∀ i j, raw29419step1 i j = -(raw29419step0 i j); unfold raw29419step1 raw29419step0; decide +kernel
      have hl : raw29419step1Labels = raw29419step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3476 node3476Labels := by rfl

def raw29420 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw29420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29420step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw29420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29420 raw29420Labels = mixedMoment B node1921 node1921Labels := by
  calc
    mixedMoment B raw29420 raw29420Labels = mixedMoment B raw29420step0 raw29420step0Labels := by
      have ha : raw29420step0 = (fun i j => raw29420 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29420step0 raw29420; decide +kernel
      have hl : raw29420step0Labels = raw29420Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29420 raw29420Labels permutation164 permutation4
    mixedMoment B raw29420step0 raw29420step0Labels = mixedMoment B raw29420step1 raw29420step1Labels := by
      have ha : raw29420step1 = -raw29420step0 := by apply Matrix.ext; change ∀ i j, raw29420step1 i j = -(raw29420step0 i j); unfold raw29420step1 raw29420step0; decide +kernel
      have hl : raw29420step1Labels = raw29420step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1921 node1921Labels := by rfl

def raw29421 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29421Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw29421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29421step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw29421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29421 raw29421Labels = mixedMoment B node3345 node3345Labels := by
  calc
    mixedMoment B raw29421 raw29421Labels = mixedMoment B raw29421step0 raw29421step0Labels := by
      have ha : raw29421step0 = (fun i j => raw29421 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29421step0 raw29421; decide +kernel
      have hl : raw29421step0Labels = raw29421Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29421 raw29421Labels permutation164 permutation4
    mixedMoment B raw29421step0 raw29421step0Labels = mixedMoment B raw29421step1 raw29421step1Labels := by
      have ha : raw29421step1 = -raw29421step0 := by apply Matrix.ext; change ∀ i j, raw29421step1 i j = -(raw29421step0 i j); unfold raw29421step1 raw29421step0; decide +kernel
      have hl : raw29421step1Labels = raw29421step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3345 node3345Labels := by rfl

def raw29422 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29422Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw29422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw29422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw29422step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29422 raw29422Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw29422 raw29422Labels = mixedMoment B raw29422step0 raw29422step0Labels := by
      have hz : ∀ j, raw29422 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29422step0 = (fun i j => raw29422 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29422step0 raw29422; decide +kernel
      have hl : raw29422step0Labels = raw29422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29422 raw29422Labels permutation434 hz
    mixedMoment B raw29422step0 raw29422step0Labels = mixedMoment B raw29422step1 raw29422step1Labels := by
      have ha : raw29422step1 = (fun i j => raw29422step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29422step1 raw29422step0; decide +kernel
      have hl : raw29422step1Labels = raw29422step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29422step0 raw29422step0Labels permutation34 permutation4
    mixedMoment B raw29422step1 raw29422step1Labels = mixedMoment B raw29422step2 raw29422step2Labels := by
      have ha : raw29422step2 = -raw29422step1 := by apply Matrix.ext; change ∀ i j, raw29422step2 i j = -(raw29422step1 i j); unfold raw29422step2 raw29422step1; decide +kernel
      have hl : raw29422step2Labels = raw29422step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3478 node3478Labels := by rfl

def raw29423 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw29423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw29423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29423 raw29423Labels = mixedMoment B node2668 node2668Labels := by
  calc
    mixedMoment B raw29423 raw29423Labels = mixedMoment B raw29423step0 raw29423step0Labels := by
      have ha : raw29423step0 = (fun i j => raw29423 (permutation577 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29423step0 raw29423; decide +kernel
      have hl : raw29423step0Labels = raw29423Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29423 raw29423Labels permutation577 permutation2
    _ = mixedMoment B node2668 node2668Labels := by rfl

def raw29424 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29424Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw29424step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw29424step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29424 raw29424Labels = mixedMoment B node3473 node3473Labels := by
  calc
    mixedMoment B raw29424 raw29424Labels = mixedMoment B raw29424step0 raw29424step0Labels := by
      have ha : raw29424step0 = (fun i j => raw29424 (permutation169 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29424step0 raw29424; decide +kernel
      have hl : raw29424step0Labels = raw29424Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29424 raw29424Labels permutation169 permutation4
    mixedMoment B raw29424step0 raw29424step0Labels = mixedMoment B raw29424step1 raw29424step1Labels := by
      have ha : raw29424step1 = -raw29424step0 := by apply Matrix.ext; change ∀ i j, raw29424step1 i j = -(raw29424step0 i j); unfold raw29424step1 raw29424step0; decide +kernel
      have hl : raw29424step1Labels = raw29424step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3473 node3473Labels := by rfl

def raw29425 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw29425Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29425step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw29425step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29425step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw29425step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29425 raw29425Labels = mixedMoment B node3473 node3473Labels := by
  calc
    mixedMoment B raw29425 raw29425Labels = mixedMoment B raw29425step0 raw29425step0Labels := by
      have ha : raw29425step0 = (fun i j => raw29425 (permutation168 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29425step0 raw29425; decide +kernel
      have hl : raw29425step0Labels = raw29425Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29425 raw29425Labels permutation168 permutation4
    mixedMoment B raw29425step0 raw29425step0Labels = mixedMoment B raw29425step1 raw29425step1Labels := by
      have ha : raw29425step1 = -raw29425step0 := by apply Matrix.ext; change ∀ i j, raw29425step1 i j = -(raw29425step0 i j); unfold raw29425step1 raw29425step0; decide +kernel
      have hl : raw29425step1Labels = raw29425step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3473 node3473Labels := by rfl

def raw29426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw29426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29426step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29426step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29426 raw29426Labels = mixedMoment B node3648 node3648Labels := by
  calc
    mixedMoment B raw29426 raw29426Labels = mixedMoment B raw29426step0 raw29426step0Labels := by
      have ha : raw29426step0 = (fun i j => raw29426 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29426step0 raw29426; decide +kernel
      have hl : raw29426step0Labels = raw29426Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29426 raw29426Labels permutation584 permutation2
    mixedMoment B raw29426step0 raw29426step0Labels = mixedMoment B raw29426step1 raw29426step1Labels := by
      have ha : raw29426step1 = -raw29426step0 := by apply Matrix.ext; change ∀ i j, raw29426step1 i j = -(raw29426step0 i j); unfold raw29426step1 raw29426step0; decide +kernel
      have hl : raw29426step1Labels = raw29426step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3648 node3648Labels := by rfl

def raw29427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29427Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw29427step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29427step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw29427step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29427 raw29427Labels = mixedMoment B node3657 node3657Labels := by
  calc
    mixedMoment B raw29427 raw29427Labels = mixedMoment B raw29427step0 raw29427step0Labels := by
      have ha : raw29427step0 = (fun i j => raw29427 (permutation587 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29427step0 raw29427; decide +kernel
      have hl : raw29427step0Labels = raw29427Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29427 raw29427Labels permutation587 permutation2
    mixedMoment B raw29427step0 raw29427step0Labels = mixedMoment B raw29427step1 raw29427step1Labels := by
      have ha : raw29427step1 = -raw29427step0 := by apply Matrix.ext; change ∀ i j, raw29427step1 i j = -(raw29427step0 i j); unfold raw29427step1 raw29427step0; decide +kernel
      have hl : raw29427step1Labels = raw29427step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3657 node3657Labels := by rfl

def raw29428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw29428Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw29428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29428step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw29428step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29428 raw29428Labels = mixedMoment B node3651 node3651Labels := by
  calc
    mixedMoment B raw29428 raw29428Labels = mixedMoment B raw29428step0 raw29428step0Labels := by
      have ha : raw29428step0 = (fun i j => raw29428 (permutation582 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29428step0 raw29428; decide +kernel
      have hl : raw29428step0Labels = raw29428Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29428 raw29428Labels permutation582 permutation2
    mixedMoment B raw29428step0 raw29428step0Labels = mixedMoment B raw29428step1 raw29428step1Labels := by
      have ha : raw29428step1 = -raw29428step0 := by apply Matrix.ext; change ∀ i j, raw29428step1 i j = -(raw29428step0 i j); unfold raw29428step1 raw29428step0; decide +kernel
      have hl : raw29428step1Labels = raw29428step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3651 node3651Labels := by rfl

def raw29429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw29429Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw29429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw29429step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29429 raw29429Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw29429 raw29429Labels = mixedMoment B raw29429step0 raw29429step0Labels := by
      have ha : raw29429step0 = (fun i j => raw29429 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29429step0 raw29429; decide +kernel
      have hl : raw29429step0Labels = raw29429Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29429 raw29429Labels permutation682 permutation2
    mixedMoment B raw29429step0 raw29429step0Labels = mixedMoment B raw29429step1 raw29429step1Labels := by
      have ha : raw29429step1 = -raw29429step0 := by apply Matrix.ext; change ∀ i j, raw29429step1 i j = -(raw29429step0 i j); unfold raw29429step1 raw29429step0; decide +kernel
      have hl : raw29429step1Labels = raw29429step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw29430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw29430Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw29430step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29430step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw29430step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29430 raw29430Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw29430 raw29430Labels = mixedMoment B raw29430step0 raw29430step0Labels := by
      have ha : raw29430step0 = (fun i j => raw29430 (permutation584 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29430step0 raw29430; decide +kernel
      have hl : raw29430step0Labels = raw29430Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29430 raw29430Labels permutation584 permutation2
    mixedMoment B raw29430step0 raw29430step0Labels = mixedMoment B raw29430step1 raw29430step1Labels := by
      have ha : raw29430step1 = -raw29430step0 := by apply Matrix.ext; change ∀ i j, raw29430step1 i j = -(raw29430step0 i j); unfold raw29430step1 raw29430step0; decide +kernel
      have hl : raw29430step1Labels = raw29430step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw29431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29431Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw29431step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw29431step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29431 raw29431Labels = mixedMoment B node3391 node3391Labels := by
  calc
    mixedMoment B raw29431 raw29431Labels = mixedMoment B raw29431step0 raw29431step0Labels := by
      have hz : ∀ j, raw29431 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29431step0 = (fun i j => raw29431 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29431step0 raw29431; decide +kernel
      have hl : raw29431step0Labels = raw29431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29431 raw29431Labels permutation434 hz
    mixedMoment B raw29431step0 raw29431step0Labels = mixedMoment B raw29431step1 raw29431step1Labels := by
      have ha : raw29431step1 = (fun i j => raw29431step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29431step1 raw29431step0; decide +kernel
      have hl : raw29431step1Labels = raw29431step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29431step0 raw29431step0Labels permutation149 permutation2
    mixedMoment B raw29431step1 raw29431step1Labels = mixedMoment B raw29431step2 raw29431step2Labels := by
      have ha : raw29431step2 = -raw29431step1 := by apply Matrix.ext; change ∀ i j, raw29431step2 i j = -(raw29431step1 i j); unfold raw29431step2 raw29431step1; decide +kernel
      have hl : raw29431step2Labels = raw29431step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3391 node3391Labels := by rfl

def raw29432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29432Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29432step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29432 raw29432Labels = mixedMoment B node2522 node2522Labels := by
  calc
    mixedMoment B raw29432 raw29432Labels = mixedMoment B raw29432step0 raw29432step0Labels := by
      have hz : ∀ j, raw29432 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29432step0 = (fun i j => raw29432 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29432step0 raw29432; decide +kernel
      have hl : raw29432step0Labels = raw29432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29432 raw29432Labels permutation434 hz
    mixedMoment B raw29432step0 raw29432step0Labels = mixedMoment B raw29432step1 raw29432step1Labels := by
      have hz : ∀ j, raw29432step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw29432step1 = (fun i j => raw29432step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw29432step1 raw29432step0; decide +kernel
      have hl : raw29432step1Labels = raw29432step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29432step0 raw29432step0Labels permutation56 hz
    _ = mixedMoment B node2522 node2522Labels := by rfl

def raw29433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw29433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29433 raw29433Labels = mixedMoment B node2560 node2560Labels := by
  calc
    mixedMoment B raw29433 raw29433Labels = mixedMoment B raw29433step0 raw29433step0Labels := by
      have hz : ∀ j, raw29433 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29433step0 = (fun i j => raw29433 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29433step0 raw29433; decide +kernel
      have hl : raw29433step0Labels = raw29433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29433 raw29433Labels permutation434 hz
    _ = mixedMoment B node2560 node2560Labels := by rfl

def raw29434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29434 raw29434Labels = mixedMoment B node2427 node2427Labels := by
  calc
    mixedMoment B raw29434 raw29434Labels = mixedMoment B raw29434step0 raw29434step0Labels := by
      have ha : raw29434step0 = (fun i j => raw29434 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29434step0 raw29434; decide +kernel
      have hl : raw29434step0Labels = raw29434Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29434 raw29434Labels permutation176 permutation2
    _ = mixedMoment B node2427 node2427Labels := by rfl

def raw29435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0], ![2, 1, -3]]
def raw29435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![3, -3, 0], ![2, 1, -3]]
def raw29435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw29435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29435 raw29435Labels = mixedMoment B node2435 node2435Labels := by
  calc
    mixedMoment B raw29435 raw29435Labels = mixedMoment B raw29435step0 raw29435step0Labels := by
      have hz : ∀ j, raw29435 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29435step0 = (fun i j => raw29435 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29435step0 raw29435; decide +kernel
      have hl : raw29435step0Labels = raw29435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29435 raw29435Labels permutation434 hz
    mixedMoment B raw29435step0 raw29435step0Labels = mixedMoment B raw29435step1 raw29435step1Labels := by
      have ha : raw29435step1 = (fun i j => raw29435step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29435step1 raw29435step0; decide +kernel
      have hl : raw29435step1Labels = raw29435step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29435step0 raw29435step0Labels permutation39 permutation2
    _ = mixedMoment B node2435 node2435Labels := by rfl

def raw29436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29436Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw29436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw29436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw29436step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29436 raw29436Labels = mixedMoment B node1807 node1807Labels := by
  calc
    mixedMoment B raw29436 raw29436Labels = mixedMoment B raw29436step0 raw29436step0Labels := by
      have hz : ∀ j, raw29436 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29436step0 = (fun i j => raw29436 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29436step0 raw29436; decide +kernel
      have hl : raw29436step0Labels = raw29436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29436 raw29436Labels permutation434 hz
    mixedMoment B raw29436step0 raw29436step0Labels = mixedMoment B raw29436step1 raw29436step1Labels := by
      have ha : raw29436step1 = (fun i j => raw29436step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29436step1 raw29436step0; decide +kernel
      have hl : raw29436step1Labels = raw29436step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29436step0 raw29436step0Labels permutation149 permutation2
    mixedMoment B raw29436step1 raw29436step1Labels = mixedMoment B raw29436step2 raw29436step2Labels := by
      have ha : raw29436step2 = -raw29436step1 := by apply Matrix.ext; change ∀ i j, raw29436step2 i j = -(raw29436step1 i j); unfold raw29436step2 raw29436step1; decide +kernel
      have hl : raw29436step2Labels = raw29436step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1807 node1807Labels := by rfl

def raw29437 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![0, 0], ![0, 0], ![3, -3]]
def raw29437Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29437step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![0, 0], ![3, -3]]
def raw29437step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29437step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![3, -3]]
def raw29437step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29437step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw29437step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29437step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw29437step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29437step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw29437step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29437 raw29437Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw29437 raw29437Labels = mixedMoment B raw29437step0 raw29437step0Labels := by
      have hz : ∀ j, raw29437 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29437step0 = (fun i j => raw29437 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29437step0 raw29437; decide +kernel
      have hl : raw29437step0Labels = raw29437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29437 raw29437Labels permutation520 hz
    mixedMoment B raw29437step0 raw29437step0Labels = mixedMoment B raw29437step1 raw29437step1Labels := by
      have hz : ∀ j, raw29437step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29437step1 = (fun i j => raw29437step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29437step1 raw29437step0; decide +kernel
      have hl : raw29437step1Labels = raw29437step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29437step0 raw29437step0Labels permutation104 hz
    mixedMoment B raw29437step1 raw29437step1Labels = mixedMoment B raw29437step2 raw29437step2Labels := by
      have hz : ∀ j, raw29437step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw29437step2 = (fun i j => raw29437step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw29437step2 raw29437step1; decide +kernel
      have hl : raw29437step2Labels = raw29437step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29437step1 raw29437step1Labels permutation14 hz
    mixedMoment B raw29437step2 raw29437step2Labels = mixedMoment B raw29437step3 raw29437step3Labels := by
      have ha : raw29437step3 = (fun i j => raw29437step2 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29437step3 raw29437step2; decide +kernel
      have hl : raw29437step3Labels = raw29437step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29437step2 raw29437step2Labels permutation7 permutation0
    mixedMoment B raw29437step3 raw29437step3Labels = mixedMoment B raw29437step4 raw29437step4Labels := by
      have ha : raw29437step4 = -raw29437step3 := by apply Matrix.ext; change ∀ i j, raw29437step4 i j = -(raw29437step3 i j); unfold raw29437step4 raw29437step3; decide +kernel
      have hl : raw29437step4Labels = raw29437step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw29438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw29438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2], ![2, -3, 1]]
def raw29438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29438 raw29438Labels = mixedMoment B node1347 node1347Labels := by
  calc
    mixedMoment B raw29438 raw29438Labels = mixedMoment B raw29438step0 raw29438step0Labels := by
      have hz : ∀ j, raw29438 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29438step0 = (fun i j => raw29438 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29438step0 raw29438; decide +kernel
      have hl : raw29438step0Labels = raw29438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29438 raw29438Labels permutation434 hz
    mixedMoment B raw29438step0 raw29438step0Labels = mixedMoment B raw29438step1 raw29438step1Labels := by
      have ha : raw29438step1 = (fun i j => raw29438step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29438step1 raw29438step0; decide +kernel
      have hl : raw29438step1Labels = raw29438step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29438step0 raw29438step0Labels permutation33 permutation2
    _ = mixedMoment B node1347 node1347Labels := by rfl

def raw29439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw29439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, 0, -2], ![2, -3, 1]]
def raw29439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw29439step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29439 raw29439Labels = mixedMoment B node2831 node2831Labels := by
  calc
    mixedMoment B raw29439 raw29439Labels = mixedMoment B raw29439step0 raw29439step0Labels := by
      have hz : ∀ j, raw29439 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29439step0 = (fun i j => raw29439 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29439step0 raw29439; decide +kernel
      have hl : raw29439step0Labels = raw29439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29439 raw29439Labels permutation434 hz
    mixedMoment B raw29439step0 raw29439step0Labels = mixedMoment B raw29439step1 raw29439step1Labels := by
      have ha : raw29439step1 = (fun i j => raw29439step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29439step1 raw29439step0; decide +kernel
      have hl : raw29439step1Labels = raw29439step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29439step0 raw29439step0Labels permutation33 permutation2
    _ = mixedMoment B node2831 node2831Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
