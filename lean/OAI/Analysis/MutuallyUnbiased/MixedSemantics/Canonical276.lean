import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw35328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35328Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35328step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35328 raw35328Labels = mixedMoment B node3409 node3409Labels := by
  calc
    mixedMoment B raw35328 raw35328Labels = mixedMoment B raw35328step0 raw35328step0Labels := by
      have ha : raw35328step0 = (fun i j => raw35328 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35328step0 raw35328; decide +kernel
      have hl : raw35328step0Labels = raw35328Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35328 raw35328Labels permutation583 permutation7
    mixedMoment B raw35328step0 raw35328step0Labels = mixedMoment B raw35328step1 raw35328step1Labels := by
      have ha : raw35328step1 = raw35328step0 := by apply Matrix.ext; unfold raw35328step1 raw35328step0; decide +kernel
      have hl : raw35328step0Labels = labelEmbedding1 ∘ raw35328step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35328step0 raw35328step0Labels raw35328step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3409 node3409Labels := by rfl

def raw35329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35329Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35329step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35329step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35329 raw35329Labels = mixedMoment B node3421 node3421Labels := by
  calc
    mixedMoment B raw35329 raw35329Labels = mixedMoment B raw35329step0 raw35329step0Labels := by
      have hz : ∀ j, raw35329 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35329step0 = (fun i j => raw35329 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35329step0 raw35329; decide +kernel
      have hl : raw35329step0Labels = raw35329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35329 raw35329Labels permutation346 hz
    mixedMoment B raw35329step0 raw35329step0Labels = mixedMoment B raw35329step1 raw35329step1Labels := by
      have ha : raw35329step1 = (fun i j => raw35329step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35329step1 raw35329step0; decide +kernel
      have hl : raw35329step1Labels = raw35329step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35329step0 raw35329step0Labels permutation126 permutation7
    mixedMoment B raw35329step1 raw35329step1Labels = mixedMoment B raw35329step2 raw35329step2Labels := by
      have ha : raw35329step2 = raw35329step1 := by apply Matrix.ext; unfold raw35329step2 raw35329step1; decide +kernel
      have hl : raw35329step1Labels = labelEmbedding1 ∘ raw35329step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35329step1 raw35329step1Labels raw35329step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3421 node3421Labels := by rfl

def raw35330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw35330Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![3, -1, -2], ![1, 0, -1]]
def raw35330step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35330step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35330 raw35330Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw35330 raw35330Labels = mixedMoment B raw35330step0 raw35330step0Labels := by
      have hz : ∀ j, raw35330 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35330step0 = (fun i j => raw35330 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35330step0 raw35330; decide +kernel
      have hl : raw35330step0Labels = raw35330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35330 raw35330Labels permutation346 hz
    mixedMoment B raw35330step0 raw35330step0Labels = mixedMoment B raw35330step1 raw35330step1Labels := by
      have ha : raw35330step1 = (fun i j => raw35330step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35330step1 raw35330step0; decide +kernel
      have hl : raw35330step1Labels = raw35330step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35330step0 raw35330step0Labels permutation126 permutation7
    mixedMoment B raw35330step1 raw35330step1Labels = mixedMoment B raw35330step2 raw35330step2Labels := by
      have ha : raw35330step2 = raw35330step1 := by apply Matrix.ext; unfold raw35330step2 raw35330step1; decide +kernel
      have hl : raw35330step1Labels = labelEmbedding1 ∘ raw35330step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35330step1 raw35330step1Labels raw35330step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3482 node3482Labels := by rfl

def raw35331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35331Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35331step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw35331step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw35331step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35331step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw35331step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35331 raw35331Labels = mixedMoment B node3415 node3415Labels := by
  calc
    mixedMoment B raw35331 raw35331Labels = mixedMoment B raw35331step0 raw35331step0Labels := by
      have hz : ∀ j, raw35331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35331step0 = (fun i j => raw35331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35331step0 raw35331; decide +kernel
      have hl : raw35331step0Labels = raw35331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35331 raw35331Labels permutation346 hz
    mixedMoment B raw35331step0 raw35331step0Labels = mixedMoment B raw35331step1 raw35331step1Labels := by
      have ha : raw35331step1 = (fun i j => raw35331step0 (permutation58 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35331step1 raw35331step0; decide +kernel
      have hl : raw35331step1Labels = raw35331step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35331step0 raw35331step0Labels permutation58 permutation5
    mixedMoment B raw35331step1 raw35331step1Labels = mixedMoment B raw35331step2 raw35331step2Labels := by
      have ha : raw35331step2 = -raw35331step1 := by apply Matrix.ext; change ∀ i j, raw35331step2 i j = -(raw35331step1 i j); unfold raw35331step2 raw35331step1; decide +kernel
      have hl : raw35331step2Labels = raw35331step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35331step2 raw35331step2Labels = mixedMoment B raw35331step3 raw35331step3Labels := by
      have ha : raw35331step3 = raw35331step2 := by apply Matrix.ext; unfold raw35331step3 raw35331step2; decide +kernel
      have hl : raw35331step2Labels = labelEmbedding1 ∘ raw35331step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35331step2 raw35331step2Labels raw35331step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3415 node3415Labels := by rfl

def raw35332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35332Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35332step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35332step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35332 raw35332Labels = mixedMoment B node3511 node3511Labels := by
  calc
    mixedMoment B raw35332 raw35332Labels = mixedMoment B raw35332step0 raw35332step0Labels := by
      have ha : raw35332step0 = (fun i j => raw35332 (permutation663 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35332step0 raw35332; decide +kernel
      have hl : raw35332step0Labels = raw35332Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35332 raw35332Labels permutation663 permutation5
    mixedMoment B raw35332step0 raw35332step0Labels = mixedMoment B raw35332step1 raw35332step1Labels := by
      have ha : raw35332step1 = raw35332step0 := by apply Matrix.ext; unfold raw35332step1 raw35332step0; decide +kernel
      have hl : raw35332step0Labels = labelEmbedding1 ∘ raw35332step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35332step0 raw35332step0Labels raw35332step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3511 node3511Labels := by rfl

def raw35333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35333Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35333step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35333step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35333step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![1, 1, -2]]
def raw35333step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35333 raw35333Labels = mixedMoment B node3592 node3592Labels := by
  calc
    mixedMoment B raw35333 raw35333Labels = mixedMoment B raw35333step0 raw35333step0Labels := by
      have hz : ∀ j, raw35333 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35333step0 = (fun i j => raw35333 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35333step0 raw35333; decide +kernel
      have hl : raw35333step0Labels = raw35333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35333 raw35333Labels permutation346 hz
    mixedMoment B raw35333step0 raw35333step0Labels = mixedMoment B raw35333step1 raw35333step1Labels := by
      have ha : raw35333step1 = (fun i j => raw35333step0 (permutation150 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35333step1 raw35333step0; decide +kernel
      have hl : raw35333step1Labels = raw35333step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35333step0 raw35333step0Labels permutation150 permutation5
    mixedMoment B raw35333step1 raw35333step1Labels = mixedMoment B raw35333step2 raw35333step2Labels := by
      have ha : raw35333step2 = raw35333step1 := by apply Matrix.ext; unfold raw35333step2 raw35333step1; decide +kernel
      have hl : raw35333step1Labels = labelEmbedding1 ∘ raw35333step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35333step1 raw35333step1Labels raw35333step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3592 node3592Labels := by rfl

def raw35334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35334Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35334 raw35334Labels = mixedMoment B node2822 node2822Labels := by
  calc
    mixedMoment B raw35334 raw35334Labels = mixedMoment B raw35334step0 raw35334step0Labels := by
      have ha : raw35334step0 = (fun i j => raw35334 (permutation272 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35334step0 raw35334; decide +kernel
      have hl : raw35334step0Labels = raw35334Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35334 raw35334Labels permutation272 permutation2
    _ = mixedMoment B node2822 node2822Labels := by rfl

def raw35335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35335step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35335 raw35335Labels = mixedMoment B node3672 node3672Labels := by
  calc
    mixedMoment B raw35335 raw35335Labels = mixedMoment B raw35335step0 raw35335step0Labels := by
      have ha : raw35335step0 = (fun i j => raw35335 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35335step0 raw35335; decide +kernel
      have hl : raw35335step0Labels = raw35335Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35335 raw35335Labels permutation583 permutation2
    mixedMoment B raw35335step0 raw35335step0Labels = mixedMoment B raw35335step1 raw35335step1Labels := by
      have ha : raw35335step1 = -raw35335step0 := by apply Matrix.ext; change ∀ i j, raw35335step1 i j = -(raw35335step0 i j); unfold raw35335step1 raw35335step0; decide +kernel
      have hl : raw35335step1Labels = raw35335step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3672 node3672Labels := by rfl

def raw35336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35336 raw35336Labels = mixedMoment B node3920 node3920Labels := by
  calc
    mixedMoment B raw35336 raw35336Labels = mixedMoment B raw35336step0 raw35336step0Labels := by
      have ha : raw35336step0 = (fun i j => raw35336 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35336step0 raw35336; decide +kernel
      have hl : raw35336step0Labels = raw35336Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35336 raw35336Labels permutation158 permutation2
    _ = mixedMoment B node3920 node3920Labels := by rfl

def raw35337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35337step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35337step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35337 raw35337Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw35337 raw35337Labels = mixedMoment B raw35337step0 raw35337step0Labels := by
      have ha : raw35337step0 = (fun i j => raw35337 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35337step0 raw35337; decide +kernel
      have hl : raw35337step0Labels = raw35337Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35337 raw35337Labels permutation583 permutation2
    mixedMoment B raw35337step0 raw35337step0Labels = mixedMoment B raw35337step1 raw35337step1Labels := by
      have ha : raw35337step1 = -raw35337step0 := by apply Matrix.ext; change ∀ i j, raw35337step1 i j = -(raw35337step0 i j); unfold raw35337step1 raw35337step0; decide +kernel
      have hl : raw35337step1Labels = raw35337step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3779 node3779Labels := by rfl

def raw35338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw35338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35338 raw35338Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw35338 raw35338Labels = mixedMoment B raw35338step0 raw35338step0Labels := by
      have ha : raw35338step0 = (fun i j => raw35338 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35338step0 raw35338; decide +kernel
      have hl : raw35338step0Labels = raw35338Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35338 raw35338Labels permutation588 permutation2
    mixedMoment B raw35338step0 raw35338step0Labels = mixedMoment B raw35338step1 raw35338step1Labels := by
      have ha : raw35338step1 = -raw35338step0 := by apply Matrix.ext; change ∀ i j, raw35338step1 i j = -(raw35338step0 i j); unfold raw35338step1 raw35338step0; decide +kernel
      have hl : raw35338step1Labels = raw35338step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3690 node3690Labels := by rfl

def raw35339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw35339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35339step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35339step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35339 raw35339Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw35339 raw35339Labels = mixedMoment B raw35339step0 raw35339step0Labels := by
      have ha : raw35339step0 = (fun i j => raw35339 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35339step0 raw35339; decide +kernel
      have hl : raw35339step0Labels = raw35339Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35339 raw35339Labels permutation589 permutation2
    mixedMoment B raw35339step0 raw35339step0Labels = mixedMoment B raw35339step1 raw35339step1Labels := by
      have ha : raw35339step1 = -raw35339step0 := by apply Matrix.ext; change ∀ i j, raw35339step1 i j = -(raw35339step0 i j); unfold raw35339step1 raw35339step0; decide +kernel
      have hl : raw35339step1Labels = raw35339step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3690 node3690Labels := by rfl

def raw35340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35340Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35340step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35340step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35340 raw35340Labels = mixedMoment B node3675 node3675Labels := by
  calc
    mixedMoment B raw35340 raw35340Labels = mixedMoment B raw35340step0 raw35340step0Labels := by
      have ha : raw35340step0 = (fun i j => raw35340 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35340step0 raw35340; decide +kernel
      have hl : raw35340step0Labels = raw35340Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35340 raw35340Labels permutation588 permutation2
    mixedMoment B raw35340step0 raw35340step0Labels = mixedMoment B raw35340step1 raw35340step1Labels := by
      have ha : raw35340step1 = -raw35340step0 := by apply Matrix.ext; change ∀ i j, raw35340step1 i j = -(raw35340step0 i j); unfold raw35340step1 raw35340step0; decide +kernel
      have hl : raw35340step1Labels = raw35340step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3675 node3675Labels := by rfl

def raw35341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw35341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35341step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35341 raw35341Labels = mixedMoment B node2322 node2322Labels := by
  calc
    mixedMoment B raw35341 raw35341Labels = mixedMoment B raw35341step0 raw35341step0Labels := by
      have ha : raw35341step0 = (fun i j => raw35341 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35341step0 raw35341; decide +kernel
      have hl : raw35341step0Labels = raw35341Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35341 raw35341Labels permutation588 permutation2
    mixedMoment B raw35341step0 raw35341step0Labels = mixedMoment B raw35341step1 raw35341step1Labels := by
      have ha : raw35341step1 = -raw35341step0 := by apply Matrix.ext; change ∀ i j, raw35341step1 i j = -(raw35341step0 i j); unfold raw35341step1 raw35341step0; decide +kernel
      have hl : raw35341step1Labels = raw35341step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2322 node2322Labels := by rfl

def raw35342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35342Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35342step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35342step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35342step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35342step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35342 raw35342Labels = mixedMoment B node2799 node2799Labels := by
  calc
    mixedMoment B raw35342 raw35342Labels = mixedMoment B raw35342step0 raw35342step0Labels := by
      have ha : raw35342step0 = (fun i j => raw35342 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35342step0 raw35342; decide +kernel
      have hl : raw35342step0Labels = raw35342Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35342 raw35342Labels permutation687 permutation2
    mixedMoment B raw35342step0 raw35342step0Labels = mixedMoment B raw35342step1 raw35342step1Labels := by
      have ha : raw35342step1 = -raw35342step0 := by apply Matrix.ext; change ∀ i j, raw35342step1 i j = -(raw35342step0 i j); unfold raw35342step1 raw35342step0; decide +kernel
      have hl : raw35342step1Labels = raw35342step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2799 node2799Labels := by rfl

def raw35343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35343Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35343step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35343step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35343 raw35343Labels = mixedMoment B node2827 node2827Labels := by
  calc
    mixedMoment B raw35343 raw35343Labels = mixedMoment B raw35343step0 raw35343step0Labels := by
      have hz : ∀ j, raw35343 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35343step0 = (fun i j => raw35343 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35343step0 raw35343; decide +kernel
      have hl : raw35343step0Labels = raw35343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35343 raw35343Labels permutation346 hz
    mixedMoment B raw35343step0 raw35343step0Labels = mixedMoment B raw35343step1 raw35343step1Labels := by
      have ha : raw35343step1 = (fun i j => raw35343step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35343step1 raw35343step0; decide +kernel
      have hl : raw35343step1Labels = raw35343step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35343step0 raw35343step0Labels permutation57 permutation2
    _ = mixedMoment B node2827 node2827Labels := by rfl

def raw35344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35344Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35344step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35344 raw35344Labels = mixedMoment B node3929 node3929Labels := by
  calc
    mixedMoment B raw35344 raw35344Labels = mixedMoment B raw35344step0 raw35344step0Labels := by
      have hz : ∀ j, raw35344 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35344step0 = (fun i j => raw35344 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35344step0 raw35344; decide +kernel
      have hl : raw35344step0Labels = raw35344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35344 raw35344Labels permutation346 hz
    _ = mixedMoment B node3929 node3929Labels := by rfl

def raw35345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35345step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35345step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35345step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35345 raw35345Labels = mixedMoment B node3790 node3790Labels := by
  calc
    mixedMoment B raw35345 raw35345Labels = mixedMoment B raw35345step0 raw35345step0Labels := by
      have hz : ∀ j, raw35345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35345step0 = (fun i j => raw35345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35345step0 raw35345; decide +kernel
      have hl : raw35345step0Labels = raw35345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35345 raw35345Labels permutation346 hz
    mixedMoment B raw35345step0 raw35345step0Labels = mixedMoment B raw35345step1 raw35345step1Labels := by
      have ha : raw35345step1 = (fun i j => raw35345step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35345step1 raw35345step0; decide +kernel
      have hl : raw35345step1Labels = raw35345step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35345step0 raw35345step0Labels permutation126 permutation2
    mixedMoment B raw35345step1 raw35345step1Labels = mixedMoment B raw35345step2 raw35345step2Labels := by
      have ha : raw35345step2 = -raw35345step1 := by apply Matrix.ext; change ∀ i j, raw35345step2 i j = -(raw35345step1 i j); unfold raw35345step2 raw35345step1; decide +kernel
      have hl : raw35345step2Labels = raw35345step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3790 node3790Labels := by rfl

def raw35346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35346step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35346step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35346step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35346step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35346 raw35346Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw35346 raw35346Labels = mixedMoment B raw35346step0 raw35346step0Labels := by
      have hz : ∀ j, raw35346 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35346step0 = (fun i j => raw35346 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35346step0 raw35346; decide +kernel
      have hl : raw35346step0Labels = raw35346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35346 raw35346Labels permutation346 hz
    mixedMoment B raw35346step0 raw35346step0Labels = mixedMoment B raw35346step1 raw35346step1Labels := by
      have ha : raw35346step1 = (fun i j => raw35346step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35346step1 raw35346step0; decide +kernel
      have hl : raw35346step1Labels = raw35346step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35346step0 raw35346step0Labels permutation57 permutation3
    mixedMoment B raw35346step1 raw35346step1Labels = mixedMoment B raw35346step2 raw35346step2Labels := by
      have ha : raw35346step2 = raw35346step1 := by apply Matrix.ext; unfold raw35346step2 raw35346step1; decide +kernel
      have hl : raw35346step1Labels = labelEmbedding6 ∘ raw35346step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35346step1 raw35346step1Labels raw35346step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw35347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw35347step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35347step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35347step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35347step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35347step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35347 raw35347Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw35347 raw35347Labels = mixedMoment B raw35347step0 raw35347step0Labels := by
      have ha : raw35347step0 = (fun i j => raw35347 (permutation585 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35347step0 raw35347; decide +kernel
      have hl : raw35347step0Labels = raw35347Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35347 raw35347Labels permutation585 permutation3
    mixedMoment B raw35347step0 raw35347step0Labels = mixedMoment B raw35347step1 raw35347step1Labels := by
      have ha : raw35347step1 = -raw35347step0 := by apply Matrix.ext; change ∀ i j, raw35347step1 i j = -(raw35347step0 i j); unfold raw35347step1 raw35347step0; decide +kernel
      have hl : raw35347step1Labels = raw35347step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35347step1 raw35347step1Labels = mixedMoment B raw35347step2 raw35347step2Labels := by
      have ha : raw35347step2 = raw35347step1 := by apply Matrix.ext; unfold raw35347step2 raw35347step1; decide +kernel
      have hl : raw35347step1Labels = labelEmbedding6 ∘ raw35347step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35347step1 raw35347step1Labels raw35347step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw35348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35348step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw35348step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35348step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35348step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35348step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35348step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35348 raw35348Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw35348 raw35348Labels = mixedMoment B raw35348step0 raw35348step0Labels := by
      have hz : ∀ j, raw35348 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35348step0 = (fun i j => raw35348 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35348step0 raw35348; decide +kernel
      have hl : raw35348step0Labels = raw35348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35348 raw35348Labels permutation346 hz
    mixedMoment B raw35348step0 raw35348step0Labels = mixedMoment B raw35348step1 raw35348step1Labels := by
      have ha : raw35348step1 = (fun i j => raw35348step0 (permutation123 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35348step1 raw35348step0; decide +kernel
      have hl : raw35348step1Labels = raw35348step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35348step0 raw35348step0Labels permutation123 permutation3
    mixedMoment B raw35348step1 raw35348step1Labels = mixedMoment B raw35348step2 raw35348step2Labels := by
      have ha : raw35348step2 = -raw35348step1 := by apply Matrix.ext; change ∀ i j, raw35348step2 i j = -(raw35348step1 i j); unfold raw35348step2 raw35348step1; decide +kernel
      have hl : raw35348step2Labels = raw35348step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35348step2 raw35348step2Labels = mixedMoment B raw35348step3 raw35348step3Labels := by
      have ha : raw35348step3 = raw35348step2 := by apply Matrix.ext; unfold raw35348step3 raw35348step2; decide +kernel
      have hl : raw35348step2Labels = labelEmbedding6 ∘ raw35348step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35348step2 raw35348step2Labels raw35348step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw35349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw35349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw35349step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw35349step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35349step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw35349step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35349step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw35349step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35349 raw35349Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw35349 raw35349Labels = mixedMoment B raw35349step0 raw35349step0Labels := by
      have hz : ∀ j, raw35349 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35349step0 = (fun i j => raw35349 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35349step0 raw35349; decide +kernel
      have hl : raw35349step0Labels = raw35349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35349 raw35349Labels permutation346 hz
    mixedMoment B raw35349step0 raw35349step0Labels = mixedMoment B raw35349step1 raw35349step1Labels := by
      have ha : raw35349step1 = (fun i j => raw35349step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35349step1 raw35349step0; decide +kernel
      have hl : raw35349step1Labels = raw35349step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35349step0 raw35349step0Labels permutation126 permutation3
    mixedMoment B raw35349step1 raw35349step1Labels = mixedMoment B raw35349step2 raw35349step2Labels := by
      have ha : raw35349step2 = -raw35349step1 := by apply Matrix.ext; change ∀ i j, raw35349step2 i j = -(raw35349step1 i j); unfold raw35349step2 raw35349step1; decide +kernel
      have hl : raw35349step2Labels = raw35349step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35349step2 raw35349step2Labels = mixedMoment B raw35349step3 raw35349step3Labels := by
      have ha : raw35349step3 = raw35349step2 := by apply Matrix.ext; unfold raw35349step3 raw35349step2; decide +kernel
      have hl : raw35349step2Labels = labelEmbedding6 ∘ raw35349step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35349step2 raw35349step2Labels raw35349step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw35350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35350step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35350step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35350step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35350step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35350 raw35350Labels = mixedMoment B node4928 node4928Labels := by
  calc
    mixedMoment B raw35350 raw35350Labels = mixedMoment B raw35350step0 raw35350step0Labels := by
      have ha : raw35350step0 = (fun i j => raw35350 (permutation272 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35350step0 raw35350; decide +kernel
      have hl : raw35350step0Labels = raw35350Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35350 raw35350Labels permutation272 permutation3
    mixedMoment B raw35350step0 raw35350step0Labels = mixedMoment B raw35350step1 raw35350step1Labels := by
      have ha : raw35350step1 = raw35350step0 := by apply Matrix.ext; unfold raw35350step1 raw35350step0; decide +kernel
      have hl : raw35350step0Labels = labelEmbedding6 ∘ raw35350step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35350step0 raw35350step0Labels raw35350step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4928 node4928Labels := by rfl

def raw35351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw35351step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35351step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw35351step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35351step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw35351step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35351 raw35351Labels = mixedMoment B node5334 node5334Labels := by
  calc
    mixedMoment B raw35351 raw35351Labels = mixedMoment B raw35351step0 raw35351step0Labels := by
      have ha : raw35351step0 = (fun i j => raw35351 (permutation583 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35351step0 raw35351; decide +kernel
      have hl : raw35351step0Labels = raw35351Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35351 raw35351Labels permutation583 permutation3
    mixedMoment B raw35351step0 raw35351step0Labels = mixedMoment B raw35351step1 raw35351step1Labels := by
      have ha : raw35351step1 = -raw35351step0 := by apply Matrix.ext; change ∀ i j, raw35351step1 i j = -(raw35351step0 i j); unfold raw35351step1 raw35351step0; decide +kernel
      have hl : raw35351step1Labels = raw35351step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35351step1 raw35351step1Labels = mixedMoment B raw35351step2 raw35351step2Labels := by
      have ha : raw35351step2 = raw35351step1 := by apply Matrix.ext; unfold raw35351step2 raw35351step1; decide +kernel
      have hl : raw35351step1Labels = labelEmbedding6 ∘ raw35351step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35351step1 raw35351step1Labels raw35351step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5334 node5334Labels := by rfl

def raw35352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw35352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35352step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35352step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35352step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35352step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35352step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35352 raw35352Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw35352 raw35352Labels = mixedMoment B raw35352step0 raw35352step0Labels := by
      have ha : raw35352step0 = (fun i j => raw35352 (permutation551 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35352step0 raw35352; decide +kernel
      have hl : raw35352step0Labels = raw35352Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35352 raw35352Labels permutation551 permutation3
    mixedMoment B raw35352step0 raw35352step0Labels = mixedMoment B raw35352step1 raw35352step1Labels := by
      have ha : raw35352step1 = -raw35352step0 := by apply Matrix.ext; change ∀ i j, raw35352step1 i j = -(raw35352step0 i j); unfold raw35352step1 raw35352step0; decide +kernel
      have hl : raw35352step1Labels = raw35352step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35352step1 raw35352step1Labels = mixedMoment B raw35352step2 raw35352step2Labels := by
      have ha : raw35352step2 = raw35352step1 := by apply Matrix.ext; unfold raw35352step2 raw35352step1; decide +kernel
      have hl : raw35352step1Labels = labelEmbedding6 ∘ raw35352step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35352step1 raw35352step1Labels raw35352step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw35353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35353step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35353step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35353step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35353 raw35353Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw35353 raw35353Labels = mixedMoment B raw35353step0 raw35353step0Labels := by
      have hz : ∀ j, raw35353 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35353step0 = (fun i j => raw35353 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35353step0 raw35353; decide +kernel
      have hl : raw35353step0Labels = raw35353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35353 raw35353Labels permutation346 hz
    mixedMoment B raw35353step0 raw35353step0Labels = mixedMoment B raw35353step1 raw35353step1Labels := by
      have ha : raw35353step1 = (fun i j => raw35353step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35353step1 raw35353step0; decide +kernel
      have hl : raw35353step1Labels = raw35353step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35353step0 raw35353step0Labels permutation57 permutation3
    mixedMoment B raw35353step1 raw35353step1Labels = mixedMoment B raw35353step2 raw35353step2Labels := by
      have ha : raw35353step2 = raw35353step1 := by apply Matrix.ext; unfold raw35353step2 raw35353step1; decide +kernel
      have hl : raw35353step1Labels = labelEmbedding6 ∘ raw35353step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35353step1 raw35353step1Labels raw35353step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4946 node4946Labels := by rfl

def raw35354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35354step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35354step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35354step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35354step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35354step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35354 raw35354Labels = mixedMoment B node5337 node5337Labels := by
  calc
    mixedMoment B raw35354 raw35354Labels = mixedMoment B raw35354step0 raw35354step0Labels := by
      have ha : raw35354step0 = (fun i j => raw35354 (permutation588 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35354step0 raw35354; decide +kernel
      have hl : raw35354step0Labels = raw35354Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35354 raw35354Labels permutation588 permutation3
    mixedMoment B raw35354step0 raw35354step0Labels = mixedMoment B raw35354step1 raw35354step1Labels := by
      have ha : raw35354step1 = -raw35354step0 := by apply Matrix.ext; change ∀ i j, raw35354step1 i j = -(raw35354step0 i j); unfold raw35354step1 raw35354step0; decide +kernel
      have hl : raw35354step1Labels = raw35354step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35354step1 raw35354step1Labels = mixedMoment B raw35354step2 raw35354step2Labels := by
      have ha : raw35354step2 = raw35354step1 := by apply Matrix.ext; unfold raw35354step2 raw35354step1; decide +kernel
      have hl : raw35354step1Labels = labelEmbedding6 ∘ raw35354step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35354step1 raw35354step1Labels raw35354step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5337 node5337Labels := by rfl

def raw35355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw35355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw35355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35355step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35355step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35355step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35355step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35355step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35355 raw35355Labels = mixedMoment B node5418 node5418Labels := by
  calc
    mixedMoment B raw35355 raw35355Labels = mixedMoment B raw35355step0 raw35355step0Labels := by
      have hz : ∀ j, raw35355 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35355step0 = (fun i j => raw35355 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35355step0 raw35355; decide +kernel
      have hl : raw35355step0Labels = raw35355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35355 raw35355Labels permutation346 hz
    mixedMoment B raw35355step0 raw35355step0Labels = mixedMoment B raw35355step1 raw35355step1Labels := by
      have ha : raw35355step1 = (fun i j => raw35355step0 (permutation120 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35355step1 raw35355step0; decide +kernel
      have hl : raw35355step1Labels = raw35355step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35355step0 raw35355step0Labels permutation120 permutation3
    mixedMoment B raw35355step1 raw35355step1Labels = mixedMoment B raw35355step2 raw35355step2Labels := by
      have ha : raw35355step2 = -raw35355step1 := by apply Matrix.ext; change ∀ i j, raw35355step2 i j = -(raw35355step1 i j); unfold raw35355step2 raw35355step1; decide +kernel
      have hl : raw35355step2Labels = raw35355step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35355step2 raw35355step2Labels = mixedMoment B raw35355step3 raw35355step3Labels := by
      have ha : raw35355step3 = raw35355step2 := by apply Matrix.ext; unfold raw35355step3 raw35355step2; decide +kernel
      have hl : raw35355step2Labels = labelEmbedding6 ∘ raw35355step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35355step2 raw35355step2Labels raw35355step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5418 node5418Labels := by rfl

def raw35356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw35356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw35356step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw35356step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35356step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw35356step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35356step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw35356step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35356 raw35356Labels = mixedMoment B node4637 node4637Labels := by
  calc
    mixedMoment B raw35356 raw35356Labels = mixedMoment B raw35356step0 raw35356step0Labels := by
      have hz : ∀ j, raw35356 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35356step0 = (fun i j => raw35356 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35356step0 raw35356; decide +kernel
      have hl : raw35356step0Labels = raw35356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35356 raw35356Labels permutation346 hz
    mixedMoment B raw35356step0 raw35356step0Labels = mixedMoment B raw35356step1 raw35356step1Labels := by
      have ha : raw35356step1 = (fun i j => raw35356step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35356step1 raw35356step0; decide +kernel
      have hl : raw35356step1Labels = raw35356step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35356step0 raw35356step0Labels permutation126 permutation3
    mixedMoment B raw35356step1 raw35356step1Labels = mixedMoment B raw35356step2 raw35356step2Labels := by
      have ha : raw35356step2 = -raw35356step1 := by apply Matrix.ext; change ∀ i j, raw35356step2 i j = -(raw35356step1 i j); unfold raw35356step2 raw35356step1; decide +kernel
      have hl : raw35356step2Labels = raw35356step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35356step2 raw35356step2Labels = mixedMoment B raw35356step3 raw35356step3Labels := by
      have ha : raw35356step3 = raw35356step2 := by apply Matrix.ext; unfold raw35356step3 raw35356step2; decide +kernel
      have hl : raw35356step2Labels = labelEmbedding6 ∘ raw35356step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35356step2 raw35356step2Labels raw35356step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4637 node4637Labels := by rfl

def raw35357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw35357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35357step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35357step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35357step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35357step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35357step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35357 raw35357Labels = mixedMoment B node4635 node4635Labels := by
  calc
    mixedMoment B raw35357 raw35357Labels = mixedMoment B raw35357step0 raw35357step0Labels := by
      have ha : raw35357step0 = (fun i j => raw35357 (permutation588 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35357step0 raw35357; decide +kernel
      have hl : raw35357step0Labels = raw35357Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35357 raw35357Labels permutation588 permutation3
    mixedMoment B raw35357step0 raw35357step0Labels = mixedMoment B raw35357step1 raw35357step1Labels := by
      have ha : raw35357step1 = -raw35357step0 := by apply Matrix.ext; change ∀ i j, raw35357step1 i j = -(raw35357step0 i j); unfold raw35357step1 raw35357step0; decide +kernel
      have hl : raw35357step1Labels = raw35357step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35357step1 raw35357step1Labels = mixedMoment B raw35357step2 raw35357step2Labels := by
      have ha : raw35357step2 = raw35357step1 := by apply Matrix.ext; unfold raw35357step2 raw35357step1; decide +kernel
      have hl : raw35357step1Labels = labelEmbedding6 ∘ raw35357step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35357step1 raw35357step1Labels raw35357step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4635 node4635Labels := by rfl

def raw35358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw35358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw35358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, -1, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw35358step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35358step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw35358step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35358step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw35358step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35358 raw35358Labels = mixedMoment B node4654 node4654Labels := by
  calc
    mixedMoment B raw35358 raw35358Labels = mixedMoment B raw35358step0 raw35358step0Labels := by
      have hz : ∀ j, raw35358 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35358step0 = (fun i j => raw35358 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35358step0 raw35358; decide +kernel
      have hl : raw35358step0Labels = raw35358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35358 raw35358Labels permutation346 hz
    mixedMoment B raw35358step0 raw35358step0Labels = mixedMoment B raw35358step1 raw35358step1Labels := by
      have ha : raw35358step1 = (fun i j => raw35358step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35358step1 raw35358step0; decide +kernel
      have hl : raw35358step1Labels = raw35358step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35358step0 raw35358step0Labels permutation126 permutation3
    mixedMoment B raw35358step1 raw35358step1Labels = mixedMoment B raw35358step2 raw35358step2Labels := by
      have ha : raw35358step2 = -raw35358step1 := by apply Matrix.ext; change ∀ i j, raw35358step2 i j = -(raw35358step1 i j); unfold raw35358step2 raw35358step1; decide +kernel
      have hl : raw35358step2Labels = raw35358step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35358step2 raw35358step2Labels = mixedMoment B raw35358step3 raw35358step3Labels := by
      have ha : raw35358step3 = raw35358step2 := by apply Matrix.ext; unfold raw35358step3 raw35358step2; decide +kernel
      have hl : raw35358step2Labels = labelEmbedding6 ∘ raw35358step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35358step2 raw35358step2Labels raw35358step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4654 node4654Labels := by rfl

def raw35359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw35359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw35359step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35359step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35359step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35359step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35359step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35359step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35359step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35359 raw35359Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw35359 raw35359Labels = mixedMoment B raw35359step0 raw35359step0Labels := by
      have hz : ∀ j, raw35359 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35359step0 = (fun i j => raw35359 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35359step0 raw35359; decide +kernel
      have hl : raw35359step0Labels = raw35359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35359 raw35359Labels permutation346 hz
    mixedMoment B raw35359step0 raw35359step0Labels = mixedMoment B raw35359step1 raw35359step1Labels := by
      have ha : raw35359step1 = (fun i j => raw35359step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35359step1 raw35359step0; decide +kernel
      have hl : raw35359step1Labels = raw35359step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35359step0 raw35359step0Labels permutation126 permutation3
    mixedMoment B raw35359step1 raw35359step1Labels = mixedMoment B raw35359step2 raw35359step2Labels := by
      have ha : raw35359step2 = -raw35359step1 := by apply Matrix.ext; change ∀ i j, raw35359step2 i j = -(raw35359step1 i j); unfold raw35359step2 raw35359step1; decide +kernel
      have hl : raw35359step2Labels = raw35359step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35359step2 raw35359step2Labels = mixedMoment B raw35359step3 raw35359step3Labels := by
      have ha : raw35359step3 = raw35359step2 := by apply Matrix.ext; unfold raw35359step3 raw35359step2; decide +kernel
      have hl : raw35359step2Labels = labelEmbedding6 ∘ raw35359step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35359step2 raw35359step2Labels raw35359step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

def raw35360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw35360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw35360step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw35360step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35360step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw35360step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35360step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw35360step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35360 raw35360Labels = mixedMoment B node4907 node4907Labels := by
  calc
    mixedMoment B raw35360 raw35360Labels = mixedMoment B raw35360step0 raw35360step0Labels := by
      have hz : ∀ j, raw35360 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35360step0 = (fun i j => raw35360 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35360step0 raw35360; decide +kernel
      have hl : raw35360step0Labels = raw35360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35360 raw35360Labels permutation346 hz
    mixedMoment B raw35360step0 raw35360step0Labels = mixedMoment B raw35360step1 raw35360step1Labels := by
      have ha : raw35360step1 = (fun i j => raw35360step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35360step1 raw35360step0; decide +kernel
      have hl : raw35360step1Labels = raw35360step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35360step0 raw35360step0Labels permutation150 permutation3
    mixedMoment B raw35360step1 raw35360step1Labels = mixedMoment B raw35360step2 raw35360step2Labels := by
      have ha : raw35360step2 = -raw35360step1 := by apply Matrix.ext; change ∀ i j, raw35360step2 i j = -(raw35360step1 i j); unfold raw35360step2 raw35360step1; decide +kernel
      have hl : raw35360step2Labels = raw35360step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35360step2 raw35360step2Labels = mixedMoment B raw35360step3 raw35360step3Labels := by
      have ha : raw35360step3 = raw35360step2 := by apply Matrix.ext; unfold raw35360step3 raw35360step2; decide +kernel
      have hl : raw35360step2Labels = labelEmbedding6 ∘ raw35360step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35360step2 raw35360step2Labels raw35360step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4907 node4907Labels := by rfl

def raw35361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw35361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35361step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35361step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35361step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35361step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35361step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35361 raw35361Labels = mixedMoment B node4906 node4906Labels := by
  calc
    mixedMoment B raw35361 raw35361Labels = mixedMoment B raw35361step0 raw35361step0Labels := by
      have ha : raw35361step0 = (fun i j => raw35361 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35361step0 raw35361; decide +kernel
      have hl : raw35361step0Labels = raw35361Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35361 raw35361Labels permutation687 permutation3
    mixedMoment B raw35361step0 raw35361step0Labels = mixedMoment B raw35361step1 raw35361step1Labels := by
      have ha : raw35361step1 = -raw35361step0 := by apply Matrix.ext; change ∀ i j, raw35361step1 i j = -(raw35361step0 i j); unfold raw35361step1 raw35361step0; decide +kernel
      have hl : raw35361step1Labels = raw35361step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35361step1 raw35361step1Labels = mixedMoment B raw35361step2 raw35361step2Labels := by
      have ha : raw35361step2 = raw35361step1 := by apply Matrix.ext; unfold raw35361step2 raw35361step1; decide +kernel
      have hl : raw35361step1Labels = labelEmbedding6 ∘ raw35361step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35361step1 raw35361step1Labels raw35361step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4906 node4906Labels := by rfl

def raw35362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw35362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw35362step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, -1, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw35362step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw35362step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35362step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw35362step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35362 raw35362Labels = mixedMoment B node4923 node4923Labels := by
  calc
    mixedMoment B raw35362 raw35362Labels = mixedMoment B raw35362step0 raw35362step0Labels := by
      have hz : ∀ j, raw35362 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35362step0 = (fun i j => raw35362 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35362step0 raw35362; decide +kernel
      have hl : raw35362step0Labels = raw35362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35362 raw35362Labels permutation346 hz
    mixedMoment B raw35362step0 raw35362step0Labels = mixedMoment B raw35362step1 raw35362step1Labels := by
      have ha : raw35362step1 = (fun i j => raw35362step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35362step1 raw35362step0; decide +kernel
      have hl : raw35362step1Labels = raw35362step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35362step0 raw35362step0Labels permutation150 permutation3
    mixedMoment B raw35362step1 raw35362step1Labels = mixedMoment B raw35362step2 raw35362step2Labels := by
      have ha : raw35362step2 = -raw35362step1 := by apply Matrix.ext; change ∀ i j, raw35362step2 i j = -(raw35362step1 i j); unfold raw35362step2 raw35362step1; decide +kernel
      have hl : raw35362step2Labels = raw35362step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35362step2 raw35362step2Labels = mixedMoment B raw35362step3 raw35362step3Labels := by
      have ha : raw35362step3 = raw35362step2 := by apply Matrix.ext; unfold raw35362step3 raw35362step2; decide +kernel
      have hl : raw35362step2Labels = labelEmbedding6 ∘ raw35362step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35362step2 raw35362step2Labels raw35362step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4923 node4923Labels := by rfl

def raw35363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35363step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35363 raw35363Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw35363 raw35363Labels = mixedMoment B raw35363step0 raw35363step0Labels := by
      have hz : ∀ j, raw35363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35363step0 = (fun i j => raw35363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35363step0 raw35363; decide +kernel
      have hl : raw35363step0Labels = raw35363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35363 raw35363Labels permutation346 hz
    mixedMoment B raw35363step0 raw35363step0Labels = mixedMoment B raw35363step1 raw35363step1Labels := by
      have ha : raw35363step1 = (fun i j => raw35363step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35363step1 raw35363step0; decide +kernel
      have hl : raw35363step1Labels = raw35363step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35363step0 raw35363step0Labels permutation57 permutation3
    _ = mixedMoment B node2561 node2561Labels := by rfl

def raw35364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35364step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw35364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35364step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35364 raw35364Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw35364 raw35364Labels = mixedMoment B raw35364step0 raw35364step0Labels := by
      have ha : raw35364step0 = (fun i j => raw35364 (permutation585 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35364step0 raw35364; decide +kernel
      have hl : raw35364step0Labels = raw35364Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35364 raw35364Labels permutation585 permutation3
    mixedMoment B raw35364step0 raw35364step0Labels = mixedMoment B raw35364step1 raw35364step1Labels := by
      have ha : raw35364step1 = -raw35364step0 := by apply Matrix.ext; change ∀ i j, raw35364step1 i j = -(raw35364step0 i j); unfold raw35364step1 raw35364step0; decide +kernel
      have hl : raw35364step1Labels = raw35364step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3690 node3690Labels := by rfl

def raw35365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35365step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw35365step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35365step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35365step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35365 raw35365Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw35365 raw35365Labels = mixedMoment B raw35365step0 raw35365step0Labels := by
      have hz : ∀ j, raw35365 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35365step0 = (fun i j => raw35365 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35365step0 raw35365; decide +kernel
      have hl : raw35365step0Labels = raw35365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35365 raw35365Labels permutation346 hz
    mixedMoment B raw35365step0 raw35365step0Labels = mixedMoment B raw35365step1 raw35365step1Labels := by
      have ha : raw35365step1 = (fun i j => raw35365step0 (permutation123 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35365step1 raw35365step0; decide +kernel
      have hl : raw35365step1Labels = raw35365step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35365step0 raw35365step0Labels permutation123 permutation3
    mixedMoment B raw35365step1 raw35365step1Labels = mixedMoment B raw35365step2 raw35365step2Labels := by
      have ha : raw35365step2 = -raw35365step1 := by apply Matrix.ext; change ∀ i j, raw35365step2 i j = -(raw35365step1 i j); unfold raw35365step2 raw35365step1; decide +kernel
      have hl : raw35365step2Labels = raw35365step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3705 node3705Labels := by rfl

def raw35366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw35366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw35366step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw35366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35366step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw35366step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35366 raw35366Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw35366 raw35366Labels = mixedMoment B raw35366step0 raw35366step0Labels := by
      have hz : ∀ j, raw35366 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35366step0 = (fun i j => raw35366 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35366step0 raw35366; decide +kernel
      have hl : raw35366step0Labels = raw35366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35366 raw35366Labels permutation346 hz
    mixedMoment B raw35366step0 raw35366step0Labels = mixedMoment B raw35366step1 raw35366step1Labels := by
      have ha : raw35366step1 = (fun i j => raw35366step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35366step1 raw35366step0; decide +kernel
      have hl : raw35366step1Labels = raw35366step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35366step0 raw35366step0Labels permutation126 permutation3
    mixedMoment B raw35366step1 raw35366step1Labels = mixedMoment B raw35366step2 raw35366step2Labels := by
      have ha : raw35366step2 = -raw35366step1 := by apply Matrix.ext; change ∀ i j, raw35366step2 i j = -(raw35366step1 i j); unfold raw35366step2 raw35366step1; decide +kernel
      have hl : raw35366step2Labels = raw35366step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw35367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35367 raw35367Labels = mixedMoment B node2318 node2318Labels := by
  calc
    mixedMoment B raw35367 raw35367Labels = mixedMoment B raw35367step0 raw35367step0Labels := by
      have ha : raw35367step0 = (fun i j => raw35367 (permutation272 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35367step0 raw35367; decide +kernel
      have hl : raw35367step0Labels = raw35367Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35367 raw35367Labels permutation272 permutation3
    _ = mixedMoment B node2318 node2318Labels := by rfl

def raw35368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw35368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35368step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw35368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35368 raw35368Labels = mixedMoment B node3669 node3669Labels := by
  calc
    mixedMoment B raw35368 raw35368Labels = mixedMoment B raw35368step0 raw35368step0Labels := by
      have ha : raw35368step0 = (fun i j => raw35368 (permutation583 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35368step0 raw35368; decide +kernel
      have hl : raw35368step0Labels = raw35368Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35368 raw35368Labels permutation583 permutation3
    mixedMoment B raw35368step0 raw35368step0Labels = mixedMoment B raw35368step1 raw35368step1Labels := by
      have ha : raw35368step1 = -raw35368step0 := by apply Matrix.ext; change ∀ i j, raw35368step1 i j = -(raw35368step0 i j); unfold raw35368step1 raw35368step0; decide +kernel
      have hl : raw35368step1Labels = raw35368step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3669 node3669Labels := by rfl

def raw35369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw35369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35369step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35369 raw35369Labels = mixedMoment B node3779 node3779Labels := by
  calc
    mixedMoment B raw35369 raw35369Labels = mixedMoment B raw35369step0 raw35369step0Labels := by
      have ha : raw35369step0 = (fun i j => raw35369 (permutation551 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35369step0 raw35369; decide +kernel
      have hl : raw35369step0Labels = raw35369Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35369 raw35369Labels permutation551 permutation3
    mixedMoment B raw35369step0 raw35369step0Labels = mixedMoment B raw35369step1 raw35369step1Labels := by
      have ha : raw35369step1 = -raw35369step0 := by apply Matrix.ext; change ∀ i j, raw35369step1 i j = -(raw35369step0 i j); unfold raw35369step1 raw35369step0; decide +kernel
      have hl : raw35369step1Labels = raw35369step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3779 node3779Labels := by rfl

def raw35370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35370 raw35370Labels = mixedMoment B node2337 node2337Labels := by
  calc
    mixedMoment B raw35370 raw35370Labels = mixedMoment B raw35370step0 raw35370step0Labels := by
      have hz : ∀ j, raw35370 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35370step0 = (fun i j => raw35370 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35370step0 raw35370; decide +kernel
      have hl : raw35370step0Labels = raw35370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35370 raw35370Labels permutation346 hz
    mixedMoment B raw35370step0 raw35370step0Labels = mixedMoment B raw35370step1 raw35370step1Labels := by
      have ha : raw35370step1 = (fun i j => raw35370step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35370step1 raw35370step0; decide +kernel
      have hl : raw35370step1Labels = raw35370step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35370step0 raw35370step0Labels permutation57 permutation3
    _ = mixedMoment B node2337 node2337Labels := by rfl

def raw35371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35371step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35371 raw35371Labels = mixedMoment B node3672 node3672Labels := by
  calc
    mixedMoment B raw35371 raw35371Labels = mixedMoment B raw35371step0 raw35371step0Labels := by
      have ha : raw35371step0 = (fun i j => raw35371 (permutation588 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35371step0 raw35371; decide +kernel
      have hl : raw35371step0Labels = raw35371Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35371 raw35371Labels permutation588 permutation3
    mixedMoment B raw35371step0 raw35371step0Labels = mixedMoment B raw35371step1 raw35371step1Labels := by
      have ha : raw35371step1 = -raw35371step0 := by apply Matrix.ext; change ∀ i j, raw35371step1 i j = -(raw35371step0 i j); unfold raw35371step1 raw35371step0; decide +kernel
      have hl : raw35371step1Labels = raw35371step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3672 node3672Labels := by rfl

def raw35372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw35372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw35372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw35372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw35372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35372 raw35372Labels = mixedMoment B node3824 node3824Labels := by
  calc
    mixedMoment B raw35372 raw35372Labels = mixedMoment B raw35372step0 raw35372step0Labels := by
      have hz : ∀ j, raw35372 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35372step0 = (fun i j => raw35372 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35372step0 raw35372; decide +kernel
      have hl : raw35372step0Labels = raw35372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35372 raw35372Labels permutation346 hz
    mixedMoment B raw35372step0 raw35372step0Labels = mixedMoment B raw35372step1 raw35372step1Labels := by
      have ha : raw35372step1 = (fun i j => raw35372step0 (permutation120 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35372step1 raw35372step0; decide +kernel
      have hl : raw35372step1Labels = raw35372step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35372step0 raw35372step0Labels permutation120 permutation3
    mixedMoment B raw35372step1 raw35372step1Labels = mixedMoment B raw35372step2 raw35372step2Labels := by
      have ha : raw35372step2 = -raw35372step1 := by apply Matrix.ext; change ∀ i j, raw35372step2 i j = -(raw35372step1 i j); unfold raw35372step2 raw35372step1; decide +kernel
      have hl : raw35372step2Labels = raw35372step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3824 node3824Labels := by rfl

def raw35373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw35373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw35373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw35373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35373step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw35373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35373 raw35373Labels = mixedMoment B node1766 node1766Labels := by
  calc
    mixedMoment B raw35373 raw35373Labels = mixedMoment B raw35373step0 raw35373step0Labels := by
      have hz : ∀ j, raw35373 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35373step0 = (fun i j => raw35373 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35373step0 raw35373; decide +kernel
      have hl : raw35373step0Labels = raw35373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35373 raw35373Labels permutation346 hz
    mixedMoment B raw35373step0 raw35373step0Labels = mixedMoment B raw35373step1 raw35373step1Labels := by
      have ha : raw35373step1 = (fun i j => raw35373step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35373step1 raw35373step0; decide +kernel
      have hl : raw35373step1Labels = raw35373step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35373step0 raw35373step0Labels permutation126 permutation3
    mixedMoment B raw35373step1 raw35373step1Labels = mixedMoment B raw35373step2 raw35373step2Labels := by
      have ha : raw35373step2 = -raw35373step1 := by apply Matrix.ext; change ∀ i j, raw35373step2 i j = -(raw35373step1 i j); unfold raw35373step2 raw35373step1; decide +kernel
      have hl : raw35373step2Labels = raw35373step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1766 node1766Labels := by rfl

def raw35374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw35374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35374step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35374 raw35374Labels = mixedMoment B node1764 node1764Labels := by
  calc
    mixedMoment B raw35374 raw35374Labels = mixedMoment B raw35374step0 raw35374step0Labels := by
      have ha : raw35374step0 = (fun i j => raw35374 (permutation588 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35374step0 raw35374; decide +kernel
      have hl : raw35374step0Labels = raw35374Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35374 raw35374Labels permutation588 permutation3
    mixedMoment B raw35374step0 raw35374step0Labels = mixedMoment B raw35374step1 raw35374step1Labels := by
      have ha : raw35374step1 = -raw35374step0 := by apply Matrix.ext; change ∀ i j, raw35374step1 i j = -(raw35374step0 i j); unfold raw35374step1 raw35374step0; decide +kernel
      have hl : raw35374step1Labels = raw35374step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1764 node1764Labels := by rfl

def raw35375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw35375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw35375step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35375step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, -1, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw35375step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35375step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw35375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35375 raw35375Labels = mixedMoment B node1782 node1782Labels := by
  calc
    mixedMoment B raw35375 raw35375Labels = mixedMoment B raw35375step0 raw35375step0Labels := by
      have hz : ∀ j, raw35375 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35375step0 = (fun i j => raw35375 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35375step0 raw35375; decide +kernel
      have hl : raw35375step0Labels = raw35375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35375 raw35375Labels permutation346 hz
    mixedMoment B raw35375step0 raw35375step0Labels = mixedMoment B raw35375step1 raw35375step1Labels := by
      have ha : raw35375step1 = (fun i j => raw35375step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35375step1 raw35375step0; decide +kernel
      have hl : raw35375step1Labels = raw35375step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35375step0 raw35375step0Labels permutation126 permutation3
    mixedMoment B raw35375step1 raw35375step1Labels = mixedMoment B raw35375step2 raw35375step2Labels := by
      have ha : raw35375step2 = -raw35375step1 := by apply Matrix.ext; change ∀ i j, raw35375step2 i j = -(raw35375step1 i j); unfold raw35375step2 raw35375step1; decide +kernel
      have hl : raw35375step2Labels = raw35375step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1782 node1782Labels := by rfl

def raw35376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw35376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw35376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35376step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35376step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35376 raw35376Labels = mixedMoment B node2029 node2029Labels := by
  calc
    mixedMoment B raw35376 raw35376Labels = mixedMoment B raw35376step0 raw35376step0Labels := by
      have hz : ∀ j, raw35376 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35376step0 = (fun i j => raw35376 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35376step0 raw35376; decide +kernel
      have hl : raw35376step0Labels = raw35376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35376 raw35376Labels permutation346 hz
    mixedMoment B raw35376step0 raw35376step0Labels = mixedMoment B raw35376step1 raw35376step1Labels := by
      have ha : raw35376step1 = (fun i j => raw35376step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35376step1 raw35376step0; decide +kernel
      have hl : raw35376step1Labels = raw35376step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35376step0 raw35376step0Labels permutation126 permutation3
    mixedMoment B raw35376step1 raw35376step1Labels = mixedMoment B raw35376step2 raw35376step2Labels := by
      have ha : raw35376step2 = -raw35376step1 := by apply Matrix.ext; change ∀ i j, raw35376step2 i j = -(raw35376step1 i j); unfold raw35376step2 raw35376step1; decide +kernel
      have hl : raw35376step2Labels = raw35376step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2029 node2029Labels := by rfl

def raw35377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw35377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw35377step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw35377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35377step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw35377step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35377 raw35377Labels = mixedMoment B node2300 node2300Labels := by
  calc
    mixedMoment B raw35377 raw35377Labels = mixedMoment B raw35377step0 raw35377step0Labels := by
      have hz : ∀ j, raw35377 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35377step0 = (fun i j => raw35377 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35377step0 raw35377; decide +kernel
      have hl : raw35377step0Labels = raw35377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35377 raw35377Labels permutation346 hz
    mixedMoment B raw35377step0 raw35377step0Labels = mixedMoment B raw35377step1 raw35377step1Labels := by
      have ha : raw35377step1 = (fun i j => raw35377step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35377step1 raw35377step0; decide +kernel
      have hl : raw35377step1Labels = raw35377step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35377step0 raw35377step0Labels permutation150 permutation3
    mixedMoment B raw35377step1 raw35377step1Labels = mixedMoment B raw35377step2 raw35377step2Labels := by
      have ha : raw35377step2 = -raw35377step1 := by apply Matrix.ext; change ∀ i j, raw35377step2 i j = -(raw35377step1 i j); unfold raw35377step2 raw35377step1; decide +kernel
      have hl : raw35377step2Labels = raw35377step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2300 node2300Labels := by rfl

def raw35378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw35378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35378step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35378 raw35378Labels = mixedMoment B node2299 node2299Labels := by
  calc
    mixedMoment B raw35378 raw35378Labels = mixedMoment B raw35378step0 raw35378step0Labels := by
      have ha : raw35378step0 = (fun i j => raw35378 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35378step0 raw35378; decide +kernel
      have hl : raw35378step0Labels = raw35378Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35378 raw35378Labels permutation687 permutation3
    mixedMoment B raw35378step0 raw35378step0Labels = mixedMoment B raw35378step1 raw35378step1Labels := by
      have ha : raw35378step1 = -raw35378step0 := by apply Matrix.ext; change ∀ i j, raw35378step1 i j = -(raw35378step0 i j); unfold raw35378step1 raw35378step0; decide +kernel
      have hl : raw35378step1Labels = raw35378step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2299 node2299Labels := by rfl

def raw35379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw35379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw35379step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35379step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, -1, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw35379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35379step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw35379step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35379 raw35379Labels = mixedMoment B node2314 node2314Labels := by
  calc
    mixedMoment B raw35379 raw35379Labels = mixedMoment B raw35379step0 raw35379step0Labels := by
      have hz : ∀ j, raw35379 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35379step0 = (fun i j => raw35379 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35379step0 raw35379; decide +kernel
      have hl : raw35379step0Labels = raw35379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35379 raw35379Labels permutation346 hz
    mixedMoment B raw35379step0 raw35379step0Labels = mixedMoment B raw35379step1 raw35379step1Labels := by
      have ha : raw35379step1 = (fun i j => raw35379step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35379step1 raw35379step0; decide +kernel
      have hl : raw35379step1Labels = raw35379step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35379step0 raw35379step0Labels permutation150 permutation3
    mixedMoment B raw35379step1 raw35379step1Labels = mixedMoment B raw35379step2 raw35379step2Labels := by
      have ha : raw35379step2 = -raw35379step1 := by apply Matrix.ext; change ∀ i j, raw35379step2 i j = -(raw35379step1 i j); unfold raw35379step2 raw35379step1; decide +kernel
      have hl : raw35379step2Labels = raw35379step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2314 node2314Labels := by rfl

def raw35380 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw35380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw35380step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35380step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35380step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35380step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35380step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35380step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35380 raw35380Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw35380 raw35380Labels = mixedMoment B raw35380step0 raw35380step0Labels := by
      have hz : ∀ j, raw35380 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35380step0 = (fun i j => raw35380 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35380step0 raw35380; decide +kernel
      have hl : raw35380step0Labels = raw35380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35380 raw35380Labels permutation346 hz
    mixedMoment B raw35380step0 raw35380step0Labels = mixedMoment B raw35380step1 raw35380step1Labels := by
      have ha : raw35380step1 = (fun i j => raw35380step0 (permutation126 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35380step1 raw35380step0; decide +kernel
      have hl : raw35380step1Labels = raw35380step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35380step0 raw35380step0Labels permutation126 permutation6
    mixedMoment B raw35380step1 raw35380step1Labels = mixedMoment B raw35380step2 raw35380step2Labels := by
      have ha : raw35380step2 = -raw35380step1 := by apply Matrix.ext; change ∀ i j, raw35380step2 i j = -(raw35380step1 i j); unfold raw35380step2 raw35380step1; decide +kernel
      have hl : raw35380step2Labels = raw35380step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35380step2 raw35380step2Labels = mixedMoment B raw35380step3 raw35380step3Labels := by
      have ha : raw35380step3 = raw35380step2 := by apply Matrix.ext; unfold raw35380step3 raw35380step2; decide +kernel
      have hl : raw35380step2Labels = labelEmbedding9 ∘ raw35380step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35380step2 raw35380step2Labels raw35380step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw35381 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw35381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw35381step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35381step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35381step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35381step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35381step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35381 raw35381Labels = mixedMoment B node5348 node5348Labels := by
  calc
    mixedMoment B raw35381 raw35381Labels = mixedMoment B raw35381step0 raw35381step0Labels := by
      have ha : raw35381step0 = (fun i j => raw35381 (permutation583 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35381step0 raw35381; decide +kernel
      have hl : raw35381step0Labels = raw35381Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35381 raw35381Labels permutation583 permutation6
    mixedMoment B raw35381step0 raw35381step0Labels = mixedMoment B raw35381step1 raw35381step1Labels := by
      have ha : raw35381step1 = -raw35381step0 := by apply Matrix.ext; change ∀ i j, raw35381step1 i j = -(raw35381step0 i j); unfold raw35381step1 raw35381step0; decide +kernel
      have hl : raw35381step1Labels = raw35381step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35381step1 raw35381step1Labels = mixedMoment B raw35381step2 raw35381step2Labels := by
      have ha : raw35381step2 = raw35381step1 := by apply Matrix.ext; unfold raw35381step2 raw35381step1; decide +kernel
      have hl : raw35381step1Labels = labelEmbedding9 ∘ raw35381step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35381step1 raw35381step1Labels raw35381step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5348 node5348Labels := by rfl

def raw35382 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw35382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw35382step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw35382step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35382step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35382step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35382step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35382step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35382 raw35382Labels = mixedMoment B node5361 node5361Labels := by
  calc
    mixedMoment B raw35382 raw35382Labels = mixedMoment B raw35382step0 raw35382step0Labels := by
      have hz : ∀ j, raw35382 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35382step0 = (fun i j => raw35382 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35382step0 raw35382; decide +kernel
      have hl : raw35382step0Labels = raw35382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35382 raw35382Labels permutation346 hz
    mixedMoment B raw35382step0 raw35382step0Labels = mixedMoment B raw35382step1 raw35382step1Labels := by
      have ha : raw35382step1 = (fun i j => raw35382step0 (permutation126 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35382step1 raw35382step0; decide +kernel
      have hl : raw35382step1Labels = raw35382step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35382step0 raw35382step0Labels permutation126 permutation6
    mixedMoment B raw35382step1 raw35382step1Labels = mixedMoment B raw35382step2 raw35382step2Labels := by
      have ha : raw35382step2 = -raw35382step1 := by apply Matrix.ext; change ∀ i j, raw35382step2 i j = -(raw35382step1 i j); unfold raw35382step2 raw35382step1; decide +kernel
      have hl : raw35382step2Labels = raw35382step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35382step2 raw35382step2Labels = mixedMoment B raw35382step3 raw35382step3Labels := by
      have ha : raw35382step3 = raw35382step2 := by apply Matrix.ext; unfold raw35382step3 raw35382step2; decide +kernel
      have hl : raw35382step2Labels = labelEmbedding9 ∘ raw35382step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35382step2 raw35382step2Labels raw35382step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5361 node5361Labels := by rfl

def raw35383 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw35383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw35383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35383step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35383step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35383step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35383 raw35383Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw35383 raw35383Labels = mixedMoment B raw35383step0 raw35383step0Labels := by
      have hz : ∀ j, raw35383 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35383step0 = (fun i j => raw35383 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35383step0 raw35383; decide +kernel
      have hl : raw35383step0Labels = raw35383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35383 raw35383Labels permutation346 hz
    mixedMoment B raw35383step0 raw35383step0Labels = mixedMoment B raw35383step1 raw35383step1Labels := by
      have ha : raw35383step1 = (fun i j => raw35383step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35383step1 raw35383step0; decide +kernel
      have hl : raw35383step1Labels = raw35383step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35383step0 raw35383step0Labels permutation32 permutation7
    mixedMoment B raw35383step1 raw35383step1Labels = mixedMoment B raw35383step2 raw35383step2Labels := by
      have ha : raw35383step2 = raw35383step1 := by apply Matrix.ext; unfold raw35383step2 raw35383step1; decide +kernel
      have hl : raw35383step1Labels = labelEmbedding10 ∘ raw35383step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35383step1 raw35383step1Labels raw35383step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw35384 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw35384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw35384step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35384step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35384step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35384step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35384step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35384 raw35384Labels = mixedMoment B node5348 node5348Labels := by
  calc
    mixedMoment B raw35384 raw35384Labels = mixedMoment B raw35384step0 raw35384step0Labels := by
      have ha : raw35384step0 = (fun i j => raw35384 (permutation584 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35384step0 raw35384; decide +kernel
      have hl : raw35384step0Labels = raw35384Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35384 raw35384Labels permutation584 permutation6
    mixedMoment B raw35384step0 raw35384step0Labels = mixedMoment B raw35384step1 raw35384step1Labels := by
      have ha : raw35384step1 = -raw35384step0 := by apply Matrix.ext; change ∀ i j, raw35384step1 i j = -(raw35384step0 i j); unfold raw35384step1 raw35384step0; decide +kernel
      have hl : raw35384step1Labels = raw35384step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35384step1 raw35384step1Labels = mixedMoment B raw35384step2 raw35384step2Labels := by
      have ha : raw35384step2 = raw35384step1 := by apply Matrix.ext; unfold raw35384step2 raw35384step1; decide +kernel
      have hl : raw35384step1Labels = labelEmbedding9 ∘ raw35384step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35384step1 raw35384step1Labels raw35384step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5348 node5348Labels := by rfl

def raw35385 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw35385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw35385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw35385step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35385step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35385step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35385step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35385 raw35385Labels = mixedMoment B node5361 node5361Labels := by
  calc
    mixedMoment B raw35385 raw35385Labels = mixedMoment B raw35385step0 raw35385step0Labels := by
      have hz : ∀ j, raw35385 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35385step0 = (fun i j => raw35385 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35385step0 raw35385; decide +kernel
      have hl : raw35385step0Labels = raw35385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35385 raw35385Labels permutation346 hz
    mixedMoment B raw35385step0 raw35385step0Labels = mixedMoment B raw35385step1 raw35385step1Labels := by
      have ha : raw35385step1 = (fun i j => raw35385step0 (permutation127 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35385step1 raw35385step0; decide +kernel
      have hl : raw35385step1Labels = raw35385step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35385step0 raw35385step0Labels permutation127 permutation6
    mixedMoment B raw35385step1 raw35385step1Labels = mixedMoment B raw35385step2 raw35385step2Labels := by
      have ha : raw35385step2 = -raw35385step1 := by apply Matrix.ext; change ∀ i j, raw35385step2 i j = -(raw35385step1 i j); unfold raw35385step2 raw35385step1; decide +kernel
      have hl : raw35385step2Labels = raw35385step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35385step2 raw35385step2Labels = mixedMoment B raw35385step3 raw35385step3Labels := by
      have ha : raw35385step3 = raw35385step2 := by apply Matrix.ext; unfold raw35385step3 raw35385step2; decide +kernel
      have hl : raw35385step2Labels = labelEmbedding9 ∘ raw35385step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35385step2 raw35385step2Labels raw35385step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5361 node5361Labels := by rfl

def raw35386 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw35386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw35386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35386step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35386step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35386step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35386 raw35386Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw35386 raw35386Labels = mixedMoment B raw35386step0 raw35386step0Labels := by
      have hz : ∀ j, raw35386 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35386step0 = (fun i j => raw35386 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35386step0 raw35386; decide +kernel
      have hl : raw35386step0Labels = raw35386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35386 raw35386Labels permutation346 hz
    mixedMoment B raw35386step0 raw35386step0Labels = mixedMoment B raw35386step1 raw35386step1Labels := by
      have ha : raw35386step1 = (fun i j => raw35386step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35386step1 raw35386step0; decide +kernel
      have hl : raw35386step1Labels = raw35386step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35386step0 raw35386step0Labels permutation56 permutation7
    mixedMoment B raw35386step1 raw35386step1Labels = mixedMoment B raw35386step2 raw35386step2Labels := by
      have ha : raw35386step2 = raw35386step1 := by apply Matrix.ext; unfold raw35386step2 raw35386step1; decide +kernel
      have hl : raw35386step1Labels = labelEmbedding10 ∘ raw35386step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35386step1 raw35386step1Labels raw35386step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw35387 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw35387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35387step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35387step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35387 raw35387Labels = mixedMoment B node5341 node5341Labels := by
  calc
    mixedMoment B raw35387 raw35387Labels = mixedMoment B raw35387step0 raw35387step0Labels := by
      have ha : raw35387step0 = (fun i j => raw35387 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35387step0 raw35387; decide +kernel
      have hl : raw35387step0Labels = raw35387Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35387 raw35387Labels permutation159 permutation6
    mixedMoment B raw35387step0 raw35387step0Labels = mixedMoment B raw35387step1 raw35387step1Labels := by
      have ha : raw35387step1 = raw35387step0 := by apply Matrix.ext; unfold raw35387step1 raw35387step0; decide +kernel
      have hl : raw35387step0Labels = labelEmbedding9 ∘ raw35387step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35387step0 raw35387step0Labels raw35387step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5341 node5341Labels := by rfl

def raw35388 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw35388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35388step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35388step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35388step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35388 raw35388Labels = mixedMoment B node5341 node5341Labels := by
  calc
    mixedMoment B raw35388 raw35388Labels = mixedMoment B raw35388step0 raw35388step0Labels := by
      have ha : raw35388step0 = (fun i j => raw35388 (permutation272 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35388step0 raw35388; decide +kernel
      have hl : raw35388step0Labels = raw35388Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35388 raw35388Labels permutation272 permutation6
    mixedMoment B raw35388step0 raw35388step0Labels = mixedMoment B raw35388step1 raw35388step1Labels := by
      have ha : raw35388step1 = raw35388step0 := by apply Matrix.ext; unfold raw35388step1 raw35388step0; decide +kernel
      have hl : raw35388step0Labels = labelEmbedding9 ∘ raw35388step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35388step0 raw35388step0Labels raw35388step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5341 node5341Labels := by rfl

def raw35389 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw35389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw35389step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35389step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw35389step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35389step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw35389step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35389 raw35389Labels = mixedMoment B node5343 node5343Labels := by
  calc
    mixedMoment B raw35389 raw35389Labels = mixedMoment B raw35389step0 raw35389step0Labels := by
      have ha : raw35389step0 = (fun i j => raw35389 (permutation583 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35389step0 raw35389; decide +kernel
      have hl : raw35389step0Labels = raw35389Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35389 raw35389Labels permutation583 permutation6
    mixedMoment B raw35389step0 raw35389step0Labels = mixedMoment B raw35389step1 raw35389step1Labels := by
      have ha : raw35389step1 = -raw35389step0 := by apply Matrix.ext; change ∀ i j, raw35389step1 i j = -(raw35389step0 i j); unfold raw35389step1 raw35389step0; decide +kernel
      have hl : raw35389step1Labels = raw35389step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35389step1 raw35389step1Labels = mixedMoment B raw35389step2 raw35389step2Labels := by
      have ha : raw35389step2 = raw35389step1 := by apply Matrix.ext; unfold raw35389step2 raw35389step1; decide +kernel
      have hl : raw35389step1Labels = labelEmbedding9 ∘ raw35389step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35389step1 raw35389step1Labels raw35389step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5343 node5343Labels := by rfl

def raw35390 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw35390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35390step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35390step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35390step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35390step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35390step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35390 raw35390Labels = mixedMoment B node5377 node5377Labels := by
  calc
    mixedMoment B raw35390 raw35390Labels = mixedMoment B raw35390step0 raw35390step0Labels := by
      have ha : raw35390step0 = (fun i j => raw35390 (permutation583 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35390step0 raw35390; decide +kernel
      have hl : raw35390step0Labels = raw35390Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35390 raw35390Labels permutation583 permutation6
    mixedMoment B raw35390step0 raw35390step0Labels = mixedMoment B raw35390step1 raw35390step1Labels := by
      have ha : raw35390step1 = -raw35390step0 := by apply Matrix.ext; change ∀ i j, raw35390step1 i j = -(raw35390step0 i j); unfold raw35390step1 raw35390step0; decide +kernel
      have hl : raw35390step1Labels = raw35390step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35390step1 raw35390step1Labels = mixedMoment B raw35390step2 raw35390step2Labels := by
      have ha : raw35390step2 = raw35390step1 := by apply Matrix.ext; unfold raw35390step2 raw35390step1; decide +kernel
      have hl : raw35390step1Labels = labelEmbedding9 ∘ raw35390step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35390step1 raw35390step1Labels raw35390step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5377 node5377Labels := by rfl

def raw35391 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw35391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw35391step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35391step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35391step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35391step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35391 raw35391Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw35391 raw35391Labels = mixedMoment B raw35391step0 raw35391step0Labels := by
      have hz : ∀ j, raw35391 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35391step0 = (fun i j => raw35391 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35391step0 raw35391; decide +kernel
      have hl : raw35391step0Labels = raw35391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35391 raw35391Labels permutation346 hz
    mixedMoment B raw35391step0 raw35391step0Labels = mixedMoment B raw35391step1 raw35391step1Labels := by
      have ha : raw35391step1 = (fun i j => raw35391step0 (permutation127 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35391step1 raw35391step0; decide +kernel
      have hl : raw35391step1Labels = raw35391step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35391step0 raw35391step0Labels permutation127 permutation4
    mixedMoment B raw35391step1 raw35391step1Labels = mixedMoment B raw35391step2 raw35391step2Labels := by
      have ha : raw35391step2 = raw35391step1 := by apply Matrix.ext; unfold raw35391step2 raw35391step1; decide +kernel
      have hl : raw35391step1Labels = labelEmbedding7 ∘ raw35391step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35391step1 raw35391step1Labels raw35391step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

def raw35392 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw35392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw35392step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35392step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35392step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35392step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw35392step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35392 raw35392Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw35392 raw35392Labels = mixedMoment B raw35392step0 raw35392step0Labels := by
      have hz : ∀ j, raw35392 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35392step0 = (fun i j => raw35392 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35392step0 raw35392; decide +kernel
      have hl : raw35392step0Labels = raw35392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35392 raw35392Labels permutation346 hz
    mixedMoment B raw35392step0 raw35392step0Labels = mixedMoment B raw35392step1 raw35392step1Labels := by
      have ha : raw35392step1 = (fun i j => raw35392step0 (permutation126 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35392step1 raw35392step0; decide +kernel
      have hl : raw35392step1Labels = raw35392step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35392step0 raw35392step0Labels permutation126 permutation4
    mixedMoment B raw35392step1 raw35392step1Labels = mixedMoment B raw35392step2 raw35392step2Labels := by
      have ha : raw35392step2 = raw35392step1 := by apply Matrix.ext; unfold raw35392step2 raw35392step1; decide +kernel
      have hl : raw35392step1Labels = labelEmbedding7 ∘ raw35392step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35392step1 raw35392step1Labels raw35392step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

def raw35393 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw35393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35393step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35393step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35393step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35393 raw35393Labels = mixedMoment B node5012 node5012Labels := by
  calc
    mixedMoment B raw35393 raw35393Labels = mixedMoment B raw35393step0 raw35393step0Labels := by
      have ha : raw35393step0 = (fun i j => raw35393 (permutation583 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35393step0 raw35393; decide +kernel
      have hl : raw35393step0Labels = raw35393Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35393 raw35393Labels permutation583 permutation4
    mixedMoment B raw35393step0 raw35393step0Labels = mixedMoment B raw35393step1 raw35393step1Labels := by
      have ha : raw35393step1 = raw35393step0 := by apply Matrix.ext; unfold raw35393step1 raw35393step0; decide +kernel
      have hl : raw35393step0Labels = labelEmbedding7 ∘ raw35393step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35393step0 raw35393step0Labels raw35393step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5012 node5012Labels := by rfl

def raw35394 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw35394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-2, 2, 0], ![1, -3, 2], ![-1, -1, 2]]
def raw35394step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw35394step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35394step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw35394step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35394 raw35394Labels = mixedMoment B node5020 node5020Labels := by
  calc
    mixedMoment B raw35394 raw35394Labels = mixedMoment B raw35394step0 raw35394step0Labels := by
      have hz : ∀ j, raw35394 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35394step0 = (fun i j => raw35394 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35394step0 raw35394; decide +kernel
      have hl : raw35394step0Labels = raw35394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35394 raw35394Labels permutation346 hz
    mixedMoment B raw35394step0 raw35394step0Labels = mixedMoment B raw35394step1 raw35394step1Labels := by
      have ha : raw35394step1 = (fun i j => raw35394step0 (permutation122 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35394step1 raw35394step0; decide +kernel
      have hl : raw35394step1Labels = raw35394step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35394step0 raw35394step0Labels permutation122 permutation4
    mixedMoment B raw35394step1 raw35394step1Labels = mixedMoment B raw35394step2 raw35394step2Labels := by
      have ha : raw35394step2 = raw35394step1 := by apply Matrix.ext; unfold raw35394step2 raw35394step1; decide +kernel
      have hl : raw35394step1Labels = labelEmbedding7 ∘ raw35394step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35394step1 raw35394step1Labels raw35394step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5020 node5020Labels := by rfl

def raw35395 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw35395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw35395step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35395step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw35395step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35395 raw35395Labels = mixedMoment B node5236 node5236Labels := by
  calc
    mixedMoment B raw35395 raw35395Labels = mixedMoment B raw35395step0 raw35395step0Labels := by
      have hz : ∀ j, raw35395 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35395step0 = (fun i j => raw35395 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35395step0 raw35395; decide +kernel
      have hl : raw35395step0Labels = raw35395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35395 raw35395Labels permutation346 hz
    mixedMoment B raw35395step0 raw35395step0Labels = mixedMoment B raw35395step1 raw35395step1Labels := by
      have ha : raw35395step1 = (fun i j => raw35395step0 (permutation126 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35395step1 raw35395step0; decide +kernel
      have hl : raw35395step1Labels = raw35395step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35395step0 raw35395step0Labels permutation126 permutation4
    mixedMoment B raw35395step1 raw35395step1Labels = mixedMoment B raw35395step2 raw35395step2Labels := by
      have ha : raw35395step2 = raw35395step1 := by apply Matrix.ext; unfold raw35395step2 raw35395step1; decide +kernel
      have hl : raw35395step1Labels = labelEmbedding7 ∘ raw35395step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35395step1 raw35395step1Labels raw35395step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5236 node5236Labels := by rfl

def raw35396 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw35396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw35396step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw35396step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35396step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35396step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35396step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35396step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35396 raw35396Labels = mixedMoment B node5327 node5327Labels := by
  calc
    mixedMoment B raw35396 raw35396Labels = mixedMoment B raw35396step0 raw35396step0Labels := by
      have hz : ∀ j, raw35396 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35396step0 = (fun i j => raw35396 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35396step0 raw35396; decide +kernel
      have hl : raw35396step0Labels = raw35396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35396 raw35396Labels permutation346 hz
    mixedMoment B raw35396step0 raw35396step0Labels = mixedMoment B raw35396step1 raw35396step1Labels := by
      have ha : raw35396step1 = (fun i j => raw35396step0 (permutation127 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35396step1 raw35396step0; decide +kernel
      have hl : raw35396step1Labels = raw35396step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35396step0 raw35396step0Labels permutation127 permutation6
    mixedMoment B raw35396step1 raw35396step1Labels = mixedMoment B raw35396step2 raw35396step2Labels := by
      have ha : raw35396step2 = -raw35396step1 := by apply Matrix.ext; change ∀ i j, raw35396step2 i j = -(raw35396step1 i j); unfold raw35396step2 raw35396step1; decide +kernel
      have hl : raw35396step2Labels = raw35396step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35396step2 raw35396step2Labels = mixedMoment B raw35396step3 raw35396step3Labels := by
      have ha : raw35396step3 = raw35396step2 := by apply Matrix.ext; unfold raw35396step3 raw35396step2; decide +kernel
      have hl : raw35396step2Labels = labelEmbedding9 ∘ raw35396step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35396step2 raw35396step2Labels raw35396step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5327 node5327Labels := by rfl

def raw35397 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw35397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw35397step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw35397step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35397step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35397step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35397step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35397step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35397 raw35397Labels = mixedMoment B node5327 node5327Labels := by
  calc
    mixedMoment B raw35397 raw35397Labels = mixedMoment B raw35397step0 raw35397step0Labels := by
      have hz : ∀ j, raw35397 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35397step0 = (fun i j => raw35397 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35397step0 raw35397; decide +kernel
      have hl : raw35397step0Labels = raw35397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35397 raw35397Labels permutation346 hz
    mixedMoment B raw35397step0 raw35397step0Labels = mixedMoment B raw35397step1 raw35397step1Labels := by
      have ha : raw35397step1 = (fun i j => raw35397step0 (permutation126 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35397step1 raw35397step0; decide +kernel
      have hl : raw35397step1Labels = raw35397step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35397step0 raw35397step0Labels permutation126 permutation6
    mixedMoment B raw35397step1 raw35397step1Labels = mixedMoment B raw35397step2 raw35397step2Labels := by
      have ha : raw35397step2 = -raw35397step1 := by apply Matrix.ext; change ∀ i j, raw35397step2 i j = -(raw35397step1 i j); unfold raw35397step2 raw35397step1; decide +kernel
      have hl : raw35397step2Labels = raw35397step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35397step2 raw35397step2Labels = mixedMoment B raw35397step3 raw35397step3Labels := by
      have ha : raw35397step3 = raw35397step2 := by apply Matrix.ext; unfold raw35397step3 raw35397step2; decide +kernel
      have hl : raw35397step2Labels = labelEmbedding9 ∘ raw35397step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35397step2 raw35397step2Labels raw35397step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5327 node5327Labels := by rfl

def raw35398 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw35398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35398step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35398step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35398step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35398step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35398 raw35398Labels = mixedMoment B node5321 node5321Labels := by
  calc
    mixedMoment B raw35398 raw35398Labels = mixedMoment B raw35398step0 raw35398step0Labels := by
      have ha : raw35398step0 = (fun i j => raw35398 (permutation583 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35398step0 raw35398; decide +kernel
      have hl : raw35398step0Labels = raw35398Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35398 raw35398Labels permutation583 permutation6
    mixedMoment B raw35398step0 raw35398step0Labels = mixedMoment B raw35398step1 raw35398step1Labels := by
      have ha : raw35398step1 = -raw35398step0 := by apply Matrix.ext; change ∀ i j, raw35398step1 i j = -(raw35398step0 i j); unfold raw35398step1 raw35398step0; decide +kernel
      have hl : raw35398step1Labels = raw35398step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35398step1 raw35398step1Labels = mixedMoment B raw35398step2 raw35398step2Labels := by
      have ha : raw35398step2 = raw35398step1 := by apply Matrix.ext; unfold raw35398step2 raw35398step1; decide +kernel
      have hl : raw35398step1Labels = labelEmbedding9 ∘ raw35398step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35398step1 raw35398step1Labels raw35398step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5321 node5321Labels := by rfl

def raw35399 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw35399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw35399step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw35399step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35399step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw35399step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35399step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw35399step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35399 raw35399Labels = mixedMoment B node5330 node5330Labels := by
  calc
    mixedMoment B raw35399 raw35399Labels = mixedMoment B raw35399step0 raw35399step0Labels := by
      have hz : ∀ j, raw35399 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35399step0 = (fun i j => raw35399 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35399step0 raw35399; decide +kernel
      have hl : raw35399step0Labels = raw35399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35399 raw35399Labels permutation346 hz
    mixedMoment B raw35399step0 raw35399step0Labels = mixedMoment B raw35399step1 raw35399step1Labels := by
      have ha : raw35399step1 = (fun i j => raw35399step0 (permutation126 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35399step1 raw35399step0; decide +kernel
      have hl : raw35399step1Labels = raw35399step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35399step0 raw35399step0Labels permutation126 permutation6
    mixedMoment B raw35399step1 raw35399step1Labels = mixedMoment B raw35399step2 raw35399step2Labels := by
      have ha : raw35399step2 = -raw35399step1 := by apply Matrix.ext; change ∀ i j, raw35399step2 i j = -(raw35399step1 i j); unfold raw35399step2 raw35399step1; decide +kernel
      have hl : raw35399step2Labels = raw35399step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35399step2 raw35399step2Labels = mixedMoment B raw35399step3 raw35399step3Labels := by
      have ha : raw35399step3 = raw35399step2 := by apply Matrix.ext; unfold raw35399step3 raw35399step2; decide +kernel
      have hl : raw35399step2Labels = labelEmbedding9 ∘ raw35399step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35399step2 raw35399step2Labels raw35399step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5330 node5330Labels := by rfl

def raw35400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw35400Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw35400step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35400step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35400step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35400 raw35400Labels = mixedMoment B node3665 node3665Labels := by
  calc
    mixedMoment B raw35400 raw35400Labels = mixedMoment B raw35400step0 raw35400step0Labels := by
      have hz : ∀ j, raw35400 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35400step0 = (fun i j => raw35400 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35400step0 raw35400; decide +kernel
      have hl : raw35400step0Labels = raw35400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35400 raw35400Labels permutation346 hz
    mixedMoment B raw35400step0 raw35400step0Labels = mixedMoment B raw35400step1 raw35400step1Labels := by
      have ha : raw35400step1 = (fun i j => raw35400step0 (permutation123 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35400step1 raw35400step0; decide +kernel
      have hl : raw35400step1Labels = raw35400step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35400step0 raw35400step0Labels permutation123 permutation2
    mixedMoment B raw35400step1 raw35400step1Labels = mixedMoment B raw35400step2 raw35400step2Labels := by
      have ha : raw35400step2 = -raw35400step1 := by apply Matrix.ext; change ∀ i j, raw35400step2 i j = -(raw35400step1 i j); unfold raw35400step2 raw35400step1; decide +kernel
      have hl : raw35400step2Labels = raw35400step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3665 node3665Labels := by rfl

def raw35401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw35401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw35401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35401step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw35401step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35401 raw35401Labels = mixedMoment B node3639 node3639Labels := by
  calc
    mixedMoment B raw35401 raw35401Labels = mixedMoment B raw35401step0 raw35401step0Labels := by
      have ha : raw35401step0 = (fun i j => raw35401 (permutation583 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35401step0 raw35401; decide +kernel
      have hl : raw35401step0Labels = raw35401Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35401 raw35401Labels permutation583 permutation2
    mixedMoment B raw35401step0 raw35401step0Labels = mixedMoment B raw35401step1 raw35401step1Labels := by
      have ha : raw35401step1 = -raw35401step0 := by apply Matrix.ext; change ∀ i j, raw35401step1 i j = -(raw35401step0 i j); unfold raw35401step1 raw35401step0; decide +kernel
      have hl : raw35401step1Labels = raw35401step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3639 node3639Labels := by rfl

def raw35402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw35402Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw35402step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw35402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35402step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw35402step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35402 raw35402Labels = mixedMoment B node3661 node3661Labels := by
  calc
    mixedMoment B raw35402 raw35402Labels = mixedMoment B raw35402step0 raw35402step0Labels := by
      have hz : ∀ j, raw35402 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35402step0 = (fun i j => raw35402 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35402step0 raw35402; decide +kernel
      have hl : raw35402step0Labels = raw35402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35402 raw35402Labels permutation346 hz
    mixedMoment B raw35402step0 raw35402step0Labels = mixedMoment B raw35402step1 raw35402step1Labels := by
      have ha : raw35402step1 = (fun i j => raw35402step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35402step1 raw35402step0; decide +kernel
      have hl : raw35402step1Labels = raw35402step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35402step0 raw35402step0Labels permutation126 permutation2
    mixedMoment B raw35402step1 raw35402step1Labels = mixedMoment B raw35402step2 raw35402step2Labels := by
      have ha : raw35402step2 = -raw35402step1 := by apply Matrix.ext; change ∀ i j, raw35402step2 i j = -(raw35402step1 i j); unfold raw35402step2 raw35402step1; decide +kernel
      have hl : raw35402step2Labels = raw35402step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3661 node3661Labels := by rfl

def raw35403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![3, -1, -2], ![2, 0, -2]]
def raw35403Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, -1, 2], ![3, -1, -2], ![2, 0, -2]]
def raw35403step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, -1, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw35403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35403step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw35403step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35403 raw35403Labels = mixedMoment B node2314 node2314Labels := by
  calc
    mixedMoment B raw35403 raw35403Labels = mixedMoment B raw35403step0 raw35403step0Labels := by
      have hz : ∀ j, raw35403 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35403step0 = (fun i j => raw35403 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35403step0 raw35403; decide +kernel
      have hl : raw35403step0Labels = raw35403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35403 raw35403Labels permutation346 hz
    mixedMoment B raw35403step0 raw35403step0Labels = mixedMoment B raw35403step1 raw35403step1Labels := by
      have ha : raw35403step1 = (fun i j => raw35403step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35403step1 raw35403step0; decide +kernel
      have hl : raw35403step1Labels = raw35403step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35403step0 raw35403step0Labels permutation126 permutation2
    mixedMoment B raw35403step1 raw35403step1Labels = mixedMoment B raw35403step2 raw35403step2Labels := by
      have ha : raw35403step2 = -raw35403step1 := by apply Matrix.ext; change ∀ i j, raw35403step2 i j = -(raw35403step1 i j); unfold raw35403step2 raw35403step1; decide +kernel
      have hl : raw35403step2Labels = raw35403step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2314 node2314Labels := by rfl

def raw35404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw35404Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw35404step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, -1, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw35404step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35404step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw35404step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35404 raw35404Labels = mixedMoment B node2314 node2314Labels := by
  calc
    mixedMoment B raw35404 raw35404Labels = mixedMoment B raw35404step0 raw35404step0Labels := by
      have hz : ∀ j, raw35404 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35404step0 = (fun i j => raw35404 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35404step0 raw35404; decide +kernel
      have hl : raw35404step0Labels = raw35404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35404 raw35404Labels permutation346 hz
    mixedMoment B raw35404step0 raw35404step0Labels = mixedMoment B raw35404step1 raw35404step1Labels := by
      have ha : raw35404step1 = (fun i j => raw35404step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35404step1 raw35404step0; decide +kernel
      have hl : raw35404step1Labels = raw35404step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35404step0 raw35404step0Labels permutation150 permutation2
    mixedMoment B raw35404step1 raw35404step1Labels = mixedMoment B raw35404step2 raw35404step2Labels := by
      have ha : raw35404step2 = -raw35404step1 := by apply Matrix.ext; change ∀ i j, raw35404step2 i j = -(raw35404step1 i j); unfold raw35404step2 raw35404step1; decide +kernel
      have hl : raw35404step2Labels = raw35404step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2314 node2314Labels := by rfl

def raw35405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35405Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw35405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35405step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35405step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35405 raw35405Labels = mixedMoment B node3652 node3652Labels := by
  calc
    mixedMoment B raw35405 raw35405Labels = mixedMoment B raw35405step0 raw35405step0Labels := by
      have ha : raw35405step0 = (fun i j => raw35405 (permutation585 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35405step0 raw35405; decide +kernel
      have hl : raw35405step0Labels = raw35405Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35405 raw35405Labels permutation585 permutation2
    mixedMoment B raw35405step0 raw35405step0Labels = mixedMoment B raw35405step1 raw35405step1Labels := by
      have ha : raw35405step1 = -raw35405step0 := by apply Matrix.ext; change ∀ i j, raw35405step1 i j = -(raw35405step0 i j); unfold raw35405step1 raw35405step0; decide +kernel
      have hl : raw35405step1Labels = raw35405step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3652 node3652Labels := by rfl

def raw35406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35406Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35406step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35406step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35406 raw35406Labels = mixedMoment B node3642 node3642Labels := by
  calc
    mixedMoment B raw35406 raw35406Labels = mixedMoment B raw35406step0 raw35406step0Labels := by
      have ha : raw35406step0 = (fun i j => raw35406 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35406step0 raw35406; decide +kernel
      have hl : raw35406step0Labels = raw35406Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35406 raw35406Labels permutation588 permutation2
    mixedMoment B raw35406step0 raw35406step0Labels = mixedMoment B raw35406step1 raw35406step1Labels := by
      have ha : raw35406step1 = -raw35406step0 := by apply Matrix.ext; change ∀ i j, raw35406step1 i j = -(raw35406step0 i j); unfold raw35406step1 raw35406step0; decide +kernel
      have hl : raw35406step1Labels = raw35406step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3642 node3642Labels := by rfl

def raw35407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw35407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35407step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35407 raw35407Labels = mixedMoment B node2299 node2299Labels := by
  calc
    mixedMoment B raw35407 raw35407Labels = mixedMoment B raw35407step0 raw35407step0Labels := by
      have ha : raw35407step0 = (fun i j => raw35407 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35407step0 raw35407; decide +kernel
      have hl : raw35407step0Labels = raw35407Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35407 raw35407Labels permutation588 permutation2
    mixedMoment B raw35407step0 raw35407step0Labels = mixedMoment B raw35407step1 raw35407step1Labels := by
      have ha : raw35407step1 = -raw35407step0 := by apply Matrix.ext; change ∀ i j, raw35407step1 i j = -(raw35407step0 i j); unfold raw35407step1 raw35407step0; decide +kernel
      have hl : raw35407step1Labels = raw35407step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2299 node2299Labels := by rfl

def raw35408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw35408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw35408step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw35408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35408 raw35408Labels = mixedMoment B node2299 node2299Labels := by
  calc
    mixedMoment B raw35408 raw35408Labels = mixedMoment B raw35408step0 raw35408step0Labels := by
      have ha : raw35408step0 = (fun i j => raw35408 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35408step0 raw35408; decide +kernel
      have hl : raw35408step0Labels = raw35408Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35408 raw35408Labels permutation687 permutation2
    mixedMoment B raw35408step0 raw35408step0Labels = mixedMoment B raw35408step1 raw35408step1Labels := by
      have ha : raw35408step1 = -raw35408step0 := by apply Matrix.ext; change ∀ i j, raw35408step1 i j = -(raw35408step0 i j); unfold raw35408step1 raw35408step0; decide +kernel
      have hl : raw35408step1Labels = raw35408step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2299 node2299Labels := by rfl

def raw35409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35409Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35409 raw35409Labels = mixedMoment B node2796 node2796Labels := by
  calc
    mixedMoment B raw35409 raw35409Labels = mixedMoment B raw35409step0 raw35409step0Labels := by
      have ha : raw35409step0 = (fun i j => raw35409 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35409step0 raw35409; decide +kernel
      have hl : raw35409step0Labels = raw35409Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35409 raw35409Labels permutation159 permutation2
    _ = mixedMoment B node2796 node2796Labels := by rfl

def raw35410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35410Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35410 raw35410Labels = mixedMoment B node2318 node2318Labels := by
  calc
    mixedMoment B raw35410 raw35410Labels = mixedMoment B raw35410step0 raw35410step0Labels := by
      have ha : raw35410step0 = (fun i j => raw35410 (permutation272 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35410step0 raw35410; decide +kernel
      have hl : raw35410step0Labels = raw35410Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35410 raw35410Labels permutation272 permutation2
    _ = mixedMoment B node2318 node2318Labels := by rfl

def raw35411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35411 raw35411Labels = mixedMoment B node3678 node3678Labels := by
  calc
    mixedMoment B raw35411 raw35411Labels = mixedMoment B raw35411step0 raw35411step0Labels := by
      have ha : raw35411step0 = (fun i j => raw35411 (permutation272 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35411step0 raw35411; decide +kernel
      have hl : raw35411step0Labels = raw35411Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35411 raw35411Labels permutation272 permutation2
    _ = mixedMoment B node3678 node3678Labels := by rfl

def raw35412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw35412Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw35412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35412 raw35412Labels = mixedMoment B node3667 node3667Labels := by
  calc
    mixedMoment B raw35412 raw35412Labels = mixedMoment B raw35412step0 raw35412step0Labels := by
      have ha : raw35412step0 = (fun i j => raw35412 (permutation272 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35412step0 raw35412; decide +kernel
      have hl : raw35412step0Labels = raw35412Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35412 raw35412Labels permutation272 permutation2
    _ = mixedMoment B node3667 node3667Labels := by rfl

def raw35413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35413Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35413 raw35413Labels = mixedMoment B node3683 node3683Labels := by
  calc
    mixedMoment B raw35413 raw35413Labels = mixedMoment B raw35413step0 raw35413step0Labels := by
      have ha : raw35413step0 = (fun i j => raw35413 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35413step0 raw35413; decide +kernel
      have hl : raw35413step0Labels = raw35413Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35413 raw35413Labels permutation271 permutation2
    _ = mixedMoment B node3683 node3683Labels := by rfl

def raw35414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw35414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35414 raw35414Labels = mixedMoment B node3682 node3682Labels := by
  calc
    mixedMoment B raw35414 raw35414Labels = mixedMoment B raw35414step0 raw35414step0Labels := by
      have ha : raw35414step0 = (fun i j => raw35414 (permutation272 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35414step0 raw35414; decide +kernel
      have hl : raw35414step0Labels = raw35414Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35414 raw35414Labels permutation272 permutation2
    _ = mixedMoment B node3682 node3682Labels := by rfl

def raw35415 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![-1, 1], ![2, -2], ![1, -1]]
def raw35415Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35415step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw35415step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical35415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35415 raw35415Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw35415 raw35415Labels = mixedMoment B raw35415step0 raw35415step0Labels := by
      have ha : raw35415step0 = (fun i j => raw35415 (permutation272 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35415step0 raw35415; decide +kernel
      have hl : raw35415step0Labels = raw35415Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35415 raw35415Labels permutation272 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw35416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35416step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw35416step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35416step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35416step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35416 raw35416Labels = mixedMoment B node5111 node5111Labels := by
  calc
    mixedMoment B raw35416 raw35416Labels = mixedMoment B raw35416step0 raw35416step0Labels := by
      have hz : ∀ j, raw35416 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35416step0 = (fun i j => raw35416 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35416step0 raw35416; decide +kernel
      have hl : raw35416step0Labels = raw35416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35416 raw35416Labels permutation434 hz
    mixedMoment B raw35416step0 raw35416step0Labels = mixedMoment B raw35416step1 raw35416step1Labels := by
      have hz : ∀ j, raw35416step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35416step1 = (fun i j => raw35416step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35416step1 raw35416step0; decide +kernel
      have hl : raw35416step1Labels = raw35416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35416step0 raw35416step0Labels permutation80 hz
    mixedMoment B raw35416step1 raw35416step1Labels = mixedMoment B raw35416step2 raw35416step2Labels := by
      have ha : raw35416step2 = (fun i j => raw35416step1 (permutation15 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35416step2 raw35416step1; decide +kernel
      have hl : raw35416step2Labels = raw35416step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35416step1 raw35416step1Labels permutation15 permutation2
    _ = mixedMoment B node5111 node5111Labels := by rfl

def raw35417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35417step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw35417step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35417step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35417step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35417 raw35417Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw35417 raw35417Labels = mixedMoment B raw35417step0 raw35417step0Labels := by
      have hz : ∀ j, raw35417 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35417step0 = (fun i j => raw35417 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35417step0 raw35417; decide +kernel
      have hl : raw35417step0Labels = raw35417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35417 raw35417Labels permutation434 hz
    mixedMoment B raw35417step0 raw35417step0Labels = mixedMoment B raw35417step1 raw35417step1Labels := by
      have ha : raw35417step1 = (fun i j => raw35417step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35417step1 raw35417step0; decide +kernel
      have hl : raw35417step1Labels = raw35417step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35417step0 raw35417step0Labels permutation126 permutation2
    mixedMoment B raw35417step1 raw35417step1Labels = mixedMoment B raw35417step2 raw35417step2Labels := by
      have ha : raw35417step2 = -raw35417step1 := by apply Matrix.ext; change ∀ i j, raw35417step2 i j = -(raw35417step1 i j); unfold raw35417step2 raw35417step1; decide +kernel
      have hl : raw35417step2Labels = raw35417step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw35418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35418step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw35418step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35418step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35418step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35418 raw35418Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw35418 raw35418Labels = mixedMoment B raw35418step0 raw35418step0Labels := by
      have hz : ∀ j, raw35418 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35418step0 = (fun i j => raw35418 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35418step0 raw35418; decide +kernel
      have hl : raw35418step0Labels = raw35418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35418 raw35418Labels permutation346 hz
    mixedMoment B raw35418step0 raw35418step0Labels = mixedMoment B raw35418step1 raw35418step1Labels := by
      have ha : raw35418step1 = (fun i j => raw35418step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35418step1 raw35418step0; decide +kernel
      have hl : raw35418step1Labels = raw35418step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35418step0 raw35418step0Labels permutation126 permutation2
    mixedMoment B raw35418step1 raw35418step1Labels = mixedMoment B raw35418step2 raw35418step2Labels := by
      have ha : raw35418step2 = -raw35418step1 := by apply Matrix.ext; change ∀ i j, raw35418step2 i j = -(raw35418step1 i j); unfold raw35418step2 raw35418step1; decide +kernel
      have hl : raw35418step2Labels = raw35418step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw35419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35419step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![2, 0, -2], ![1, 0, -1]]
def raw35419step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35419step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]
def raw35419step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw35419step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw35419step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw35419step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw35419step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical35419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35419 raw35419Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw35419 raw35419Labels = mixedMoment B raw35419step0 raw35419step0Labels := by
      have hz : ∀ j, raw35419 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35419step0 = (fun i j => raw35419 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35419step0 raw35419; decide +kernel
      have hl : raw35419step0Labels = raw35419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35419 raw35419Labels permutation434 hz
    mixedMoment B raw35419step0 raw35419step0Labels = mixedMoment B raw35419step1 raw35419step1Labels := by
      have hz : ∀ j, raw35419step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35419step1 = (fun i j => raw35419step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35419step1 raw35419step0; decide +kernel
      have hl : raw35419step1Labels = raw35419step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35419step0 raw35419step0Labels permutation80 hz
    mixedMoment B raw35419step1 raw35419step1Labels = mixedMoment B raw35419step2 raw35419step2Labels := by
      have hz : ∀ i, raw35419step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw35419step2 = (fun i j => raw35419step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw35419step2 raw35419step1; decide +kernel
      have hl : raw35419step2Labels = (fun j => raw35419step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35419step1 raw35419step1Labels permutation4 hz
    mixedMoment B raw35419step2 raw35419step2Labels = mixedMoment B raw35419step3 raw35419step3Labels := by
      have ha : raw35419step3 = (fun i j => raw35419step2 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35419step3 raw35419step2; decide +kernel
      have hl : raw35419step3Labels = raw35419step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35419step2 raw35419step2Labels permutation15 permutation0
    mixedMoment B raw35419step3 raw35419step3Labels = mixedMoment B raw35419step4 raw35419step4Labels := by
      have ha : raw35419step4 = raw35419step3 := by apply Matrix.ext; unfold raw35419step4 raw35419step3; decide +kernel
      have hl : raw35419step3Labels = labelEmbedding2 ∘ raw35419step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35419step3 raw35419step3Labels raw35419step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw35420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35420step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35420 raw35420Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw35420 raw35420Labels = mixedMoment B raw35420step0 raw35420step0Labels := by
      have hz : ∀ j, raw35420 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35420step0 = (fun i j => raw35420 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35420step0 raw35420; decide +kernel
      have hl : raw35420step0Labels = raw35420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35420 raw35420Labels permutation434 hz
    mixedMoment B raw35420step0 raw35420step0Labels = mixedMoment B raw35420step1 raw35420step1Labels := by
      have ha : raw35420step1 = (fun i j => raw35420step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35420step1 raw35420step0; decide +kernel
      have hl : raw35420step1Labels = raw35420step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35420step0 raw35420step0Labels permutation57 permutation2
    _ = mixedMoment B node4946 node4946Labels := by rfl

def raw35421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35421 raw35421Labels = mixedMoment B node5335 node5335Labels := by
  calc
    mixedMoment B raw35421 raw35421Labels = mixedMoment B raw35421step0 raw35421step0Labels := by
      have ha : raw35421step0 = (fun i j => raw35421 (permutation272 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35421step0 raw35421; decide +kernel
      have hl : raw35421step0Labels = raw35421Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35421 raw35421Labels permutation272 permutation2
    _ = mixedMoment B node5335 node5335Labels := by rfl

def raw35422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35422step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35422step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35422 raw35422Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw35422 raw35422Labels = mixedMoment B raw35422step0 raw35422step0Labels := by
      have hz : ∀ j, raw35422 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35422step0 = (fun i j => raw35422 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35422step0 raw35422; decide +kernel
      have hl : raw35422step0Labels = raw35422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35422 raw35422Labels permutation434 hz
    mixedMoment B raw35422step0 raw35422step0Labels = mixedMoment B raw35422step1 raw35422step1Labels := by
      have ha : raw35422step1 = (fun i j => raw35422step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35422step1 raw35422step0; decide +kernel
      have hl : raw35422step1Labels = raw35422step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35422step0 raw35422step0Labels permutation57 permutation2
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw35423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35423step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35423step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35423 raw35423Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw35423 raw35423Labels = mixedMoment B raw35423step0 raw35423step0Labels := by
      have hz : ∀ j, raw35423 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35423step0 = (fun i j => raw35423 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35423step0 raw35423; decide +kernel
      have hl : raw35423step0Labels = raw35423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35423 raw35423Labels permutation346 hz
    mixedMoment B raw35423step0 raw35423step0Labels = mixedMoment B raw35423step1 raw35423step1Labels := by
      have ha : raw35423step1 = (fun i j => raw35423step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35423step1 raw35423step0; decide +kernel
      have hl : raw35423step1Labels = raw35423step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35423step0 raw35423step0Labels permutation57 permutation2
    _ = mixedMoment B node4946 node4946Labels := by rfl

def raw35424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35424step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35424 raw35424Labels = mixedMoment B node5335 node5335Labels := by
  calc
    mixedMoment B raw35424 raw35424Labels = mixedMoment B raw35424step0 raw35424step0Labels := by
      have ha : raw35424step0 = (fun i j => raw35424 (permutation266 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35424step0 raw35424; decide +kernel
      have hl : raw35424step0Labels = raw35424Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35424 raw35424Labels permutation266 permutation2
    _ = mixedMoment B node5335 node5335Labels := by rfl

def raw35425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35425step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35425step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35425 raw35425Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw35425 raw35425Labels = mixedMoment B raw35425step0 raw35425step0Labels := by
      have hz : ∀ j, raw35425 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35425step0 = (fun i j => raw35425 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35425step0 raw35425; decide +kernel
      have hl : raw35425step0Labels = raw35425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35425 raw35425Labels permutation346 hz
    mixedMoment B raw35425step0 raw35425step0Labels = mixedMoment B raw35425step1 raw35425step1Labels := by
      have ha : raw35425step1 = (fun i j => raw35425step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35425step1 raw35425step0; decide +kernel
      have hl : raw35425step1Labels = raw35425step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35425step0 raw35425step0Labels permutation57 permutation2
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw35426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35426step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35426step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw35426step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35426step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw35426step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35426 raw35426Labels = mixedMoment B node4952 node4952Labels := by
  calc
    mixedMoment B raw35426 raw35426Labels = mixedMoment B raw35426step0 raw35426step0Labels := by
      have hz : ∀ j, raw35426 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35426step0 = (fun i j => raw35426 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35426step0 raw35426; decide +kernel
      have hl : raw35426step0Labels = raw35426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35426 raw35426Labels permutation434 hz
    mixedMoment B raw35426step0 raw35426step0Labels = mixedMoment B raw35426step1 raw35426step1Labels := by
      have hz : ∀ j, raw35426step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35426step1 = (fun i j => raw35426step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35426step1 raw35426step0; decide +kernel
      have hl : raw35426step1Labels = raw35426step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35426step0 raw35426step0Labels permutation80 hz
    mixedMoment B raw35426step1 raw35426step1Labels = mixedMoment B raw35426step2 raw35426step2Labels := by
      have ha : raw35426step2 = (fun i j => raw35426step1 (permutation15 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35426step2 raw35426step1; decide +kernel
      have hl : raw35426step2Labels = raw35426step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35426step1 raw35426step1Labels permutation15 permutation2
    _ = mixedMoment B node4952 node4952Labels := by rfl

def raw35427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw35427step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35427step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35427step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35427 raw35427Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw35427 raw35427Labels = mixedMoment B raw35427step0 raw35427step0Labels := by
      have hz : ∀ j, raw35427 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35427step0 = (fun i j => raw35427 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35427step0 raw35427; decide +kernel
      have hl : raw35427step0Labels = raw35427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35427 raw35427Labels permutation434 hz
    mixedMoment B raw35427step0 raw35427step0Labels = mixedMoment B raw35427step1 raw35427step1Labels := by
      have ha : raw35427step1 = (fun i j => raw35427step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35427step1 raw35427step0; decide +kernel
      have hl : raw35427step1Labels = raw35427step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35427step0 raw35427step0Labels permutation126 permutation2
    mixedMoment B raw35427step1 raw35427step1Labels = mixedMoment B raw35427step2 raw35427step2Labels := by
      have ha : raw35427step2 = -raw35427step1 := by apply Matrix.ext; change ∀ i j, raw35427step2 i j = -(raw35427step1 i j); unfold raw35427step2 raw35427step1; decide +kernel
      have hl : raw35427step2Labels = raw35427step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4946 node4946Labels := by rfl

def raw35428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35428step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw35428step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35428step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35428step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35428 raw35428Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw35428 raw35428Labels = mixedMoment B raw35428step0 raw35428step0Labels := by
      have hz : ∀ j, raw35428 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35428step0 = (fun i j => raw35428 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35428step0 raw35428; decide +kernel
      have hl : raw35428step0Labels = raw35428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35428 raw35428Labels permutation346 hz
    mixedMoment B raw35428step0 raw35428step0Labels = mixedMoment B raw35428step1 raw35428step1Labels := by
      have ha : raw35428step1 = (fun i j => raw35428step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35428step1 raw35428step0; decide +kernel
      have hl : raw35428step1Labels = raw35428step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35428step0 raw35428step0Labels permutation126 permutation2
    mixedMoment B raw35428step1 raw35428step1Labels = mixedMoment B raw35428step2 raw35428step2Labels := by
      have ha : raw35428step2 = -raw35428step1 := by apply Matrix.ext; change ∀ i j, raw35428step2 i j = -(raw35428step1 i j); unfold raw35428step2 raw35428step1; decide +kernel
      have hl : raw35428step2Labels = raw35428step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4946 node4946Labels := by rfl

def raw35429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw35429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw35429step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35429step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![3, -1, -2], ![1, 0, -1]]
def raw35429step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35429step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw35429step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35429step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35429step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35429 raw35429Labels = mixedMoment B node5111 node5111Labels := by
  calc
    mixedMoment B raw35429 raw35429Labels = mixedMoment B raw35429step0 raw35429step0Labels := by
      have hz : ∀ j, raw35429 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35429step0 = (fun i j => raw35429 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35429step0 raw35429; decide +kernel
      have hl : raw35429step0Labels = raw35429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35429 raw35429Labels permutation434 hz
    mixedMoment B raw35429step0 raw35429step0Labels = mixedMoment B raw35429step1 raw35429step1Labels := by
      have hz : ∀ j, raw35429step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35429step1 = (fun i j => raw35429step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35429step1 raw35429step0; decide +kernel
      have hl : raw35429step1Labels = raw35429step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35429step0 raw35429step0Labels permutation80 hz
    mixedMoment B raw35429step1 raw35429step1Labels = mixedMoment B raw35429step2 raw35429step2Labels := by
      have ha : raw35429step2 = (fun i j => raw35429step1 (permutation24 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35429step2 raw35429step1; decide +kernel
      have hl : raw35429step2Labels = raw35429step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35429step1 raw35429step1Labels permutation24 permutation2
    mixedMoment B raw35429step2 raw35429step2Labels = mixedMoment B raw35429step3 raw35429step3Labels := by
      have ha : raw35429step3 = -raw35429step2 := by apply Matrix.ext; change ∀ i j, raw35429step3 i j = -(raw35429step2 i j); unfold raw35429step3 raw35429step2; decide +kernel
      have hl : raw35429step3Labels = raw35429step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5111 node5111Labels := by rfl

def raw35430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35430step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35430step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw35430step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35430step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw35430step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35430 raw35430Labels = mixedMoment B node4953 node4953Labels := by
  calc
    mixedMoment B raw35430 raw35430Labels = mixedMoment B raw35430step0 raw35430step0Labels := by
      have hz : ∀ j, raw35430 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35430step0 = (fun i j => raw35430 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35430step0 raw35430; decide +kernel
      have hl : raw35430step0Labels = raw35430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35430 raw35430Labels permutation434 hz
    mixedMoment B raw35430step0 raw35430step0Labels = mixedMoment B raw35430step1 raw35430step1Labels := by
      have hz : ∀ j, raw35430step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35430step1 = (fun i j => raw35430step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35430step1 raw35430step0; decide +kernel
      have hl : raw35430step1Labels = raw35430step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35430step0 raw35430step0Labels permutation80 hz
    mixedMoment B raw35430step1 raw35430step1Labels = mixedMoment B raw35430step2 raw35430step2Labels := by
      have ha : raw35430step2 = (fun i j => raw35430step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35430step2 raw35430step1; decide +kernel
      have hl : raw35430step2Labels = raw35430step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35430step1 raw35430step1Labels permutation14 permutation2
    _ = mixedMoment B node4953 node4953Labels := by rfl

def raw35431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35431step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw35431step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35431step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35431step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35431step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35431 raw35431Labels = mixedMoment B node4977 node4977Labels := by
  calc
    mixedMoment B raw35431 raw35431Labels = mixedMoment B raw35431step0 raw35431step0Labels := by
      have hz : ∀ j, raw35431 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35431step0 = (fun i j => raw35431 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35431step0 raw35431; decide +kernel
      have hl : raw35431step0Labels = raw35431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35431 raw35431Labels permutation434 hz
    mixedMoment B raw35431step0 raw35431step0Labels = mixedMoment B raw35431step1 raw35431step1Labels := by
      have ha : raw35431step1 = (fun i j => raw35431step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35431step1 raw35431step0; decide +kernel
      have hl : raw35431step1Labels = raw35431step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35431step0 raw35431step0Labels permutation151 permutation3
    mixedMoment B raw35431step1 raw35431step1Labels = mixedMoment B raw35431step2 raw35431step2Labels := by
      have ha : raw35431step2 = -raw35431step1 := by apply Matrix.ext; change ∀ i j, raw35431step2 i j = -(raw35431step1 i j); unfold raw35431step2 raw35431step1; decide +kernel
      have hl : raw35431step2Labels = raw35431step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35431step2 raw35431step2Labels = mixedMoment B raw35431step3 raw35431step3Labels := by
      have ha : raw35431step3 = raw35431step2 := by apply Matrix.ext; unfold raw35431step3 raw35431step2; decide +kernel
      have hl : raw35431step2Labels = labelEmbedding6 ∘ raw35431step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35431step2 raw35431step2Labels raw35431step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4977 node4977Labels := by rfl

def raw35432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35432step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw35432step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35432step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35432step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35432step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw35432step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35432 raw35432Labels = mixedMoment B node4977 node4977Labels := by
  calc
    mixedMoment B raw35432 raw35432Labels = mixedMoment B raw35432step0 raw35432step0Labels := by
      have hz : ∀ j, raw35432 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35432step0 = (fun i j => raw35432 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35432step0 raw35432; decide +kernel
      have hl : raw35432step0Labels = raw35432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35432 raw35432Labels permutation346 hz
    mixedMoment B raw35432step0 raw35432step0Labels = mixedMoment B raw35432step1 raw35432step1Labels := by
      have ha : raw35432step1 = (fun i j => raw35432step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35432step1 raw35432step0; decide +kernel
      have hl : raw35432step1Labels = raw35432step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35432step0 raw35432step0Labels permutation151 permutation3
    mixedMoment B raw35432step1 raw35432step1Labels = mixedMoment B raw35432step2 raw35432step2Labels := by
      have ha : raw35432step2 = -raw35432step1 := by apply Matrix.ext; change ∀ i j, raw35432step2 i j = -(raw35432step1 i j); unfold raw35432step2 raw35432step1; decide +kernel
      have hl : raw35432step2Labels = raw35432step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35432step2 raw35432step2Labels = mixedMoment B raw35432step3 raw35432step3Labels := by
      have ha : raw35432step3 = raw35432step2 := by apply Matrix.ext; unfold raw35432step3 raw35432step2; decide +kernel
      have hl : raw35432step2Labels = labelEmbedding6 ∘ raw35432step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35432step2 raw35432step2Labels raw35432step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4977 node4977Labels := by rfl

def raw35433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35433Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35433step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35433step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw35433step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35433step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35433step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35433step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35433step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35433step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35433step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35433 raw35433Labels = mixedMoment B node3485 node3485Labels := by
  calc
    mixedMoment B raw35433 raw35433Labels = mixedMoment B raw35433step0 raw35433step0Labels := by
      have hz : ∀ j, raw35433 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35433step0 = (fun i j => raw35433 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35433step0 raw35433; decide +kernel
      have hl : raw35433step0Labels = raw35433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35433 raw35433Labels permutation434 hz
    mixedMoment B raw35433step0 raw35433step0Labels = mixedMoment B raw35433step1 raw35433step1Labels := by
      have hz : ∀ j, raw35433step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35433step1 = (fun i j => raw35433step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35433step1 raw35433step0; decide +kernel
      have hl : raw35433step1Labels = raw35433step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35433step0 raw35433step0Labels permutation80 hz
    mixedMoment B raw35433step1 raw35433step1Labels = mixedMoment B raw35433step2 raw35433step2Labels := by
      have ha : raw35433step2 = (fun i j => raw35433step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35433step2 raw35433step1; decide +kernel
      have hl : raw35433step2Labels = raw35433step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35433step1 raw35433step1Labels permutation15 permutation7
    mixedMoment B raw35433step2 raw35433step2Labels = mixedMoment B raw35433step3 raw35433step3Labels := by
      have ha : raw35433step3 = -raw35433step2 := by apply Matrix.ext; change ∀ i j, raw35433step3 i j = -(raw35433step2 i j); unfold raw35433step3 raw35433step2; decide +kernel
      have hl : raw35433step3Labels = raw35433step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35433step3 raw35433step3Labels = mixedMoment B raw35433step4 raw35433step4Labels := by
      have ha : raw35433step4 = raw35433step3 := by apply Matrix.ext; unfold raw35433step4 raw35433step3; decide +kernel
      have hl : raw35433step3Labels = labelEmbedding1 ∘ raw35433step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35433step3 raw35433step3Labels raw35433step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3485 node3485Labels := by rfl

def raw35434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35434Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35434step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35434step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35434step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35434step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35434 raw35434Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw35434 raw35434Labels = mixedMoment B raw35434step0 raw35434step0Labels := by
      have hz : ∀ j, raw35434 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35434step0 = (fun i j => raw35434 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35434step0 raw35434; decide +kernel
      have hl : raw35434step0Labels = raw35434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35434 raw35434Labels permutation434 hz
    mixedMoment B raw35434step0 raw35434step0Labels = mixedMoment B raw35434step1 raw35434step1Labels := by
      have ha : raw35434step1 = (fun i j => raw35434step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35434step1 raw35434step0; decide +kernel
      have hl : raw35434step1Labels = raw35434step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35434step0 raw35434step0Labels permutation126 permutation7
    mixedMoment B raw35434step1 raw35434step1Labels = mixedMoment B raw35434step2 raw35434step2Labels := by
      have ha : raw35434step2 = raw35434step1 := by apply Matrix.ext; unfold raw35434step2 raw35434step1; decide +kernel
      have hl : raw35434step1Labels = labelEmbedding1 ∘ raw35434step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35434step1 raw35434step1Labels raw35434step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

def raw35435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35435Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35435step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35435step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35435step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35435 raw35435Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw35435 raw35435Labels = mixedMoment B raw35435step0 raw35435step0Labels := by
      have hz : ∀ j, raw35435 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35435step0 = (fun i j => raw35435 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35435step0 raw35435; decide +kernel
      have hl : raw35435step0Labels = raw35435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35435 raw35435Labels permutation346 hz
    mixedMoment B raw35435step0 raw35435step0Labels = mixedMoment B raw35435step1 raw35435step1Labels := by
      have ha : raw35435step1 = (fun i j => raw35435step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35435step1 raw35435step0; decide +kernel
      have hl : raw35435step1Labels = raw35435step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35435step0 raw35435step0Labels permutation126 permutation7
    mixedMoment B raw35435step1 raw35435step1Labels = mixedMoment B raw35435step2 raw35435step2Labels := by
      have ha : raw35435step2 = raw35435step1 := by apply Matrix.ext; unfold raw35435step2 raw35435step1; decide +kernel
      have hl : raw35435step1Labels = labelEmbedding1 ∘ raw35435step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35435step1 raw35435step1Labels raw35435step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

def raw35436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35436Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35436step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35436step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![2, 0, -2], ![1, 0, -1]]
def raw35436step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35436step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]
def raw35436step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw35436step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw35436step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical35436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35436 raw35436Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw35436 raw35436Labels = mixedMoment B raw35436step0 raw35436step0Labels := by
      have hz : ∀ j, raw35436 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35436step0 = (fun i j => raw35436 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35436step0 raw35436; decide +kernel
      have hl : raw35436step0Labels = raw35436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35436 raw35436Labels permutation434 hz
    mixedMoment B raw35436step0 raw35436step0Labels = mixedMoment B raw35436step1 raw35436step1Labels := by
      have hz : ∀ j, raw35436step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35436step1 = (fun i j => raw35436step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35436step1 raw35436step0; decide +kernel
      have hl : raw35436step1Labels = raw35436step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35436step0 raw35436step0Labels permutation80 hz
    mixedMoment B raw35436step1 raw35436step1Labels = mixedMoment B raw35436step2 raw35436step2Labels := by
      have hz : ∀ i, raw35436step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw35436step2 = (fun i j => raw35436step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw35436step2 raw35436step1; decide +kernel
      have hl : raw35436step2Labels = (fun j => raw35436step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35436step1 raw35436step1Labels permutation4 hz
    mixedMoment B raw35436step2 raw35436step2Labels = mixedMoment B raw35436step3 raw35436step3Labels := by
      have ha : raw35436step3 = (fun i j => raw35436step2 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35436step3 raw35436step2; decide +kernel
      have hl : raw35436step3Labels = raw35436step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35436step2 raw35436step2Labels permutation15 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw35437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35437Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35437step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35437step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35437step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35437step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35437step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35437step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35437 raw35437Labels = mixedMoment B node3412 node3412Labels := by
  calc
    mixedMoment B raw35437 raw35437Labels = mixedMoment B raw35437step0 raw35437step0Labels := by
      have hz : ∀ j, raw35437 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35437step0 = (fun i j => raw35437 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35437step0 raw35437; decide +kernel
      have hl : raw35437step0Labels = raw35437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35437 raw35437Labels permutation434 hz
    mixedMoment B raw35437step0 raw35437step0Labels = mixedMoment B raw35437step1 raw35437step1Labels := by
      have ha : raw35437step1 = (fun i j => raw35437step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35437step1 raw35437step0; decide +kernel
      have hl : raw35437step1Labels = raw35437step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35437step0 raw35437step0Labels permutation57 permutation7
    mixedMoment B raw35437step1 raw35437step1Labels = mixedMoment B raw35437step2 raw35437step2Labels := by
      have ha : raw35437step2 = -raw35437step1 := by apply Matrix.ext; change ∀ i j, raw35437step2 i j = -(raw35437step1 i j); unfold raw35437step2 raw35437step1; decide +kernel
      have hl : raw35437step2Labels = raw35437step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35437step2 raw35437step2Labels = mixedMoment B raw35437step3 raw35437step3Labels := by
      have ha : raw35437step3 = raw35437step2 := by apply Matrix.ext; unfold raw35437step3 raw35437step2; decide +kernel
      have hl : raw35437step2Labels = labelEmbedding1 ∘ raw35437step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35437step2 raw35437step2Labels raw35437step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3412 node3412Labels := by rfl

def raw35438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35438Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35438step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35438step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35438 raw35438Labels = mixedMoment B node3753 node3753Labels := by
  calc
    mixedMoment B raw35438 raw35438Labels = mixedMoment B raw35438step0 raw35438step0Labels := by
      have ha : raw35438step0 = (fun i j => raw35438 (permutation583 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35438step0 raw35438; decide +kernel
      have hl : raw35438step0Labels = raw35438Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35438 raw35438Labels permutation583 permutation7
    mixedMoment B raw35438step0 raw35438step0Labels = mixedMoment B raw35438step1 raw35438step1Labels := by
      have ha : raw35438step1 = raw35438step0 := by apply Matrix.ext; unfold raw35438step1 raw35438step0; decide +kernel
      have hl : raw35438step0Labels = labelEmbedding1 ∘ raw35438step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35438step0 raw35438step0Labels raw35438step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3753 node3753Labels := by rfl

def raw35439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35439Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35439step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35439step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35439step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35439step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35439step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35439step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35439 raw35439Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw35439 raw35439Labels = mixedMoment B raw35439step0 raw35439step0Labels := by
      have hz : ∀ j, raw35439 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35439step0 = (fun i j => raw35439 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35439step0 raw35439; decide +kernel
      have hl : raw35439step0Labels = raw35439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35439 raw35439Labels permutation434 hz
    mixedMoment B raw35439step0 raw35439step0Labels = mixedMoment B raw35439step1 raw35439step1Labels := by
      have ha : raw35439step1 = (fun i j => raw35439step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35439step1 raw35439step0; decide +kernel
      have hl : raw35439step1Labels = raw35439step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35439step0 raw35439step0Labels permutation57 permutation7
    mixedMoment B raw35439step1 raw35439step1Labels = mixedMoment B raw35439step2 raw35439step2Labels := by
      have ha : raw35439step2 = -raw35439step1 := by apply Matrix.ext; change ∀ i j, raw35439step2 i j = -(raw35439step1 i j); unfold raw35439step2 raw35439step1; decide +kernel
      have hl : raw35439step2Labels = raw35439step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35439step2 raw35439step2Labels = mixedMoment B raw35439step3 raw35439step3Labels := by
      have ha : raw35439step3 = raw35439step2 := by apply Matrix.ext; unfold raw35439step3 raw35439step2; decide +kernel
      have hl : raw35439step2Labels = labelEmbedding1 ∘ raw35439step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35439step2 raw35439step2Labels raw35439step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

def raw35440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35440Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35440step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw35440step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35440step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35440step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35440step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35440step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35440 raw35440Labels = mixedMoment B node3412 node3412Labels := by
  calc
    mixedMoment B raw35440 raw35440Labels = mixedMoment B raw35440step0 raw35440step0Labels := by
      have hz : ∀ j, raw35440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35440step0 = (fun i j => raw35440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35440step0 raw35440; decide +kernel
      have hl : raw35440step0Labels = raw35440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35440 raw35440Labels permutation346 hz
    mixedMoment B raw35440step0 raw35440step0Labels = mixedMoment B raw35440step1 raw35440step1Labels := by
      have ha : raw35440step1 = (fun i j => raw35440step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35440step1 raw35440step0; decide +kernel
      have hl : raw35440step1Labels = raw35440step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35440step0 raw35440step0Labels permutation57 permutation7
    mixedMoment B raw35440step1 raw35440step1Labels = mixedMoment B raw35440step2 raw35440step2Labels := by
      have ha : raw35440step2 = -raw35440step1 := by apply Matrix.ext; change ∀ i j, raw35440step2 i j = -(raw35440step1 i j); unfold raw35440step2 raw35440step1; decide +kernel
      have hl : raw35440step2Labels = raw35440step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35440step2 raw35440step2Labels = mixedMoment B raw35440step3 raw35440step3Labels := by
      have ha : raw35440step3 = raw35440step2 := by apply Matrix.ext; unfold raw35440step3 raw35440step2; decide +kernel
      have hl : raw35440step2Labels = labelEmbedding1 ∘ raw35440step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35440step2 raw35440step2Labels raw35440step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3412 node3412Labels := by rfl

def raw35441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw35441Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35441step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35441step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35441 raw35441Labels = mixedMoment B node3753 node3753Labels := by
  calc
    mixedMoment B raw35441 raw35441Labels = mixedMoment B raw35441step0 raw35441step0Labels := by
      have ha : raw35441step0 = (fun i j => raw35441 (permutation588 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35441step0 raw35441; decide +kernel
      have hl : raw35441step0Labels = raw35441Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35441 raw35441Labels permutation588 permutation7
    mixedMoment B raw35441step0 raw35441step0Labels = mixedMoment B raw35441step1 raw35441step1Labels := by
      have ha : raw35441step1 = raw35441step0 := by apply Matrix.ext; unfold raw35441step1 raw35441step0; decide +kernel
      have hl : raw35441step0Labels = labelEmbedding1 ∘ raw35441step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35441step0 raw35441step0Labels raw35441step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3753 node3753Labels := by rfl

def raw35442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35442Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw35442step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35442step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35442step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35442step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35442step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35442 raw35442Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw35442 raw35442Labels = mixedMoment B raw35442step0 raw35442step0Labels := by
      have hz : ∀ j, raw35442 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35442step0 = (fun i j => raw35442 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35442step0 raw35442; decide +kernel
      have hl : raw35442step0Labels = raw35442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35442 raw35442Labels permutation346 hz
    mixedMoment B raw35442step0 raw35442step0Labels = mixedMoment B raw35442step1 raw35442step1Labels := by
      have ha : raw35442step1 = (fun i j => raw35442step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35442step1 raw35442step0; decide +kernel
      have hl : raw35442step1Labels = raw35442step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35442step0 raw35442step0Labels permutation57 permutation7
    mixedMoment B raw35442step1 raw35442step1Labels = mixedMoment B raw35442step2 raw35442step2Labels := by
      have ha : raw35442step2 = -raw35442step1 := by apply Matrix.ext; change ∀ i j, raw35442step2 i j = -(raw35442step1 i j); unfold raw35442step2 raw35442step1; decide +kernel
      have hl : raw35442step2Labels = raw35442step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35442step2 raw35442step2Labels = mixedMoment B raw35442step3 raw35442step3Labels := by
      have ha : raw35442step3 = raw35442step2 := by apply Matrix.ext; unfold raw35442step3 raw35442step2; decide +kernel
      have hl : raw35442step2Labels = labelEmbedding1 ∘ raw35442step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35442step2 raw35442step2Labels raw35442step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

def raw35443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35443Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35443step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35443step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw35443step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35443step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 1, -2], ![2, 1, -3]]
def raw35443step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35443step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 1, -2], ![2, 1, -3]]
def raw35443step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35443 raw35443Labels = mixedMoment B node3422 node3422Labels := by
  calc
    mixedMoment B raw35443 raw35443Labels = mixedMoment B raw35443step0 raw35443step0Labels := by
      have hz : ∀ j, raw35443 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35443step0 = (fun i j => raw35443 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35443step0 raw35443; decide +kernel
      have hl : raw35443step0Labels = raw35443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35443 raw35443Labels permutation434 hz
    mixedMoment B raw35443step0 raw35443step0Labels = mixedMoment B raw35443step1 raw35443step1Labels := by
      have hz : ∀ j, raw35443step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35443step1 = (fun i j => raw35443step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35443step1 raw35443step0; decide +kernel
      have hl : raw35443step1Labels = raw35443step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35443step0 raw35443step0Labels permutation80 hz
    mixedMoment B raw35443step1 raw35443step1Labels = mixedMoment B raw35443step2 raw35443step2Labels := by
      have ha : raw35443step2 = (fun i j => raw35443step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35443step2 raw35443step1; decide +kernel
      have hl : raw35443step2Labels = raw35443step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35443step1 raw35443step1Labels permutation24 permutation7
    mixedMoment B raw35443step2 raw35443step2Labels = mixedMoment B raw35443step3 raw35443step3Labels := by
      have ha : raw35443step3 = raw35443step2 := by apply Matrix.ext; unfold raw35443step3 raw35443step2; decide +kernel
      have hl : raw35443step2Labels = labelEmbedding1 ∘ raw35443step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35443step2 raw35443step2Labels raw35443step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3422 node3422Labels := by rfl

def raw35444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35444Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35444step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35444step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35444step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35444step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35444 raw35444Labels = mixedMoment B node3412 node3412Labels := by
  calc
    mixedMoment B raw35444 raw35444Labels = mixedMoment B raw35444step0 raw35444step0Labels := by
      have hz : ∀ j, raw35444 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35444step0 = (fun i j => raw35444 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35444step0 raw35444; decide +kernel
      have hl : raw35444step0Labels = raw35444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35444 raw35444Labels permutation434 hz
    mixedMoment B raw35444step0 raw35444step0Labels = mixedMoment B raw35444step1 raw35444step1Labels := by
      have ha : raw35444step1 = (fun i j => raw35444step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35444step1 raw35444step0; decide +kernel
      have hl : raw35444step1Labels = raw35444step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35444step0 raw35444step0Labels permutation126 permutation7
    mixedMoment B raw35444step1 raw35444step1Labels = mixedMoment B raw35444step2 raw35444step2Labels := by
      have ha : raw35444step2 = raw35444step1 := by apply Matrix.ext; unfold raw35444step2 raw35444step1; decide +kernel
      have hl : raw35444step1Labels = labelEmbedding1 ∘ raw35444step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35444step1 raw35444step1Labels raw35444step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3412 node3412Labels := by rfl

def raw35445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35445Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw35445step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35445step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw35445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35445 raw35445Labels = mixedMoment B node3412 node3412Labels := by
  calc
    mixedMoment B raw35445 raw35445Labels = mixedMoment B raw35445step0 raw35445step0Labels := by
      have hz : ∀ j, raw35445 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35445step0 = (fun i j => raw35445 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35445step0 raw35445; decide +kernel
      have hl : raw35445step0Labels = raw35445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35445 raw35445Labels permutation346 hz
    mixedMoment B raw35445step0 raw35445step0Labels = mixedMoment B raw35445step1 raw35445step1Labels := by
      have ha : raw35445step1 = (fun i j => raw35445step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35445step1 raw35445step0; decide +kernel
      have hl : raw35445step1Labels = raw35445step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35445step0 raw35445step0Labels permutation126 permutation7
    mixedMoment B raw35445step1 raw35445step1Labels = mixedMoment B raw35445step2 raw35445step2Labels := by
      have ha : raw35445step2 = raw35445step1 := by apply Matrix.ext; unfold raw35445step2 raw35445step1; decide +kernel
      have hl : raw35445step1Labels = labelEmbedding1 ∘ raw35445step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35445step1 raw35445step1Labels raw35445step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3412 node3412Labels := by rfl

def raw35446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw35446Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw35446step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35446step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![3, -1, -2], ![1, 0, -1]]
def raw35446step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35446step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35446step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35446step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35446step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35446 raw35446Labels = mixedMoment B node3485 node3485Labels := by
  calc
    mixedMoment B raw35446 raw35446Labels = mixedMoment B raw35446step0 raw35446step0Labels := by
      have hz : ∀ j, raw35446 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35446step0 = (fun i j => raw35446 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35446step0 raw35446; decide +kernel
      have hl : raw35446step0Labels = raw35446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35446 raw35446Labels permutation434 hz
    mixedMoment B raw35446step0 raw35446step0Labels = mixedMoment B raw35446step1 raw35446step1Labels := by
      have hz : ∀ j, raw35446step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35446step1 = (fun i j => raw35446step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35446step1 raw35446step0; decide +kernel
      have hl : raw35446step1Labels = raw35446step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35446step0 raw35446step0Labels permutation80 hz
    mixedMoment B raw35446step1 raw35446step1Labels = mixedMoment B raw35446step2 raw35446step2Labels := by
      have ha : raw35446step2 = (fun i j => raw35446step1 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35446step2 raw35446step1; decide +kernel
      have hl : raw35446step2Labels = raw35446step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35446step1 raw35446step1Labels permutation24 permutation7
    mixedMoment B raw35446step2 raw35446step2Labels = mixedMoment B raw35446step3 raw35446step3Labels := by
      have ha : raw35446step3 = raw35446step2 := by apply Matrix.ext; unfold raw35446step3 raw35446step2; decide +kernel
      have hl : raw35446step2Labels = labelEmbedding1 ∘ raw35446step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35446step2 raw35446step2Labels raw35446step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3485 node3485Labels := by rfl

def raw35447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35447Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35447step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35447step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw35447step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35447step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, -2, 3], ![-2, 0, 2]]
def raw35447step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35447step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw35447step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35447step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw35447step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35447 raw35447Labels = mixedMoment B node3423 node3423Labels := by
  calc
    mixedMoment B raw35447 raw35447Labels = mixedMoment B raw35447step0 raw35447step0Labels := by
      have hz : ∀ j, raw35447 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35447step0 = (fun i j => raw35447 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35447step0 raw35447; decide +kernel
      have hl : raw35447step0Labels = raw35447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35447 raw35447Labels permutation434 hz
    mixedMoment B raw35447step0 raw35447step0Labels = mixedMoment B raw35447step1 raw35447step1Labels := by
      have hz : ∀ j, raw35447step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw35447step1 = (fun i j => raw35447step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw35447step1 raw35447step0; decide +kernel
      have hl : raw35447step1Labels = raw35447step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35447step0 raw35447step0Labels permutation80 hz
    mixedMoment B raw35447step1 raw35447step1Labels = mixedMoment B raw35447step2 raw35447step2Labels := by
      have ha : raw35447step2 = (fun i j => raw35447step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35447step2 raw35447step1; decide +kernel
      have hl : raw35447step2Labels = raw35447step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35447step1 raw35447step1Labels permutation15 permutation7
    mixedMoment B raw35447step2 raw35447step2Labels = mixedMoment B raw35447step3 raw35447step3Labels := by
      have ha : raw35447step3 = -raw35447step2 := by apply Matrix.ext; change ∀ i j, raw35447step3 i j = -(raw35447step2 i j); unfold raw35447step3 raw35447step2; decide +kernel
      have hl : raw35447step3Labels = raw35447step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35447step3 raw35447step3Labels = mixedMoment B raw35447step4 raw35447step4Labels := by
      have ha : raw35447step4 = raw35447step3 := by apply Matrix.ext; unfold raw35447step4 raw35447step3; decide +kernel
      have hl : raw35447step3Labels = labelEmbedding1 ∘ raw35447step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35447step3 raw35447step3Labels raw35447step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3423 node3423Labels := by rfl

def raw35448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35448Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35448step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw35448step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35448step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw35448step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35448 raw35448Labels = mixedMoment B node3595 node3595Labels := by
  calc
    mixedMoment B raw35448 raw35448Labels = mixedMoment B raw35448step0 raw35448step0Labels := by
      have hz : ∀ j, raw35448 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw35448step0 = (fun i j => raw35448 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw35448step0 raw35448; decide +kernel
      have hl : raw35448step0Labels = raw35448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35448 raw35448Labels permutation434 hz
    mixedMoment B raw35448step0 raw35448step0Labels = mixedMoment B raw35448step1 raw35448step1Labels := by
      have ha : raw35448step1 = (fun i j => raw35448step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35448step1 raw35448step0; decide +kernel
      have hl : raw35448step1Labels = raw35448step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35448step0 raw35448step0Labels permutation149 permutation5
    mixedMoment B raw35448step1 raw35448step1Labels = mixedMoment B raw35448step2 raw35448step2Labels := by
      have ha : raw35448step2 = raw35448step1 := by apply Matrix.ext; unfold raw35448step2 raw35448step1; decide +kernel
      have hl : raw35448step1Labels = labelEmbedding1 ∘ raw35448step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35448step1 raw35448step1Labels raw35448step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3595 node3595Labels := by rfl

def raw35449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35449Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw35449step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw35449step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35449step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw35449step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35449 raw35449Labels = mixedMoment B node3595 node3595Labels := by
  calc
    mixedMoment B raw35449 raw35449Labels = mixedMoment B raw35449step0 raw35449step0Labels := by
      have hz : ∀ j, raw35449 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35449step0 = (fun i j => raw35449 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35449step0 raw35449; decide +kernel
      have hl : raw35449step0Labels = raw35449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35449 raw35449Labels permutation346 hz
    mixedMoment B raw35449step0 raw35449step0Labels = mixedMoment B raw35449step1 raw35449step1Labels := by
      have ha : raw35449step1 = (fun i j => raw35449step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35449step1 raw35449step0; decide +kernel
      have hl : raw35449step1Labels = raw35449step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35449step0 raw35449step0Labels permutation149 permutation5
    mixedMoment B raw35449step1 raw35449step1Labels = mixedMoment B raw35449step2 raw35449step2Labels := by
      have ha : raw35449step2 = raw35449step1 := by apply Matrix.ext; unfold raw35449step2 raw35449step1; decide +kernel
      have hl : raw35449step1Labels = labelEmbedding1 ∘ raw35449step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35449step1 raw35449step1Labels raw35449step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3595 node3595Labels := by rfl

def raw35450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35450Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35450step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35450step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35450 raw35450Labels = mixedMoment B node5063 node5063Labels := by
  calc
    mixedMoment B raw35450 raw35450Labels = mixedMoment B raw35450step0 raw35450step0Labels := by
      have hz : ∀ j, raw35450 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35450step0 = (fun i j => raw35450 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35450step0 raw35450; decide +kernel
      have hl : raw35450step0Labels = raw35450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35450 raw35450Labels permutation346 hz
    mixedMoment B raw35450step0 raw35450step0Labels = mixedMoment B raw35450step1 raw35450step1Labels := by
      have ha : raw35450step1 = (fun i j => raw35450step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35450step1 raw35450step0; decide +kernel
      have hl : raw35450step1Labels = raw35450step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35450step0 raw35450step0Labels permutation56 permutation2
    _ = mixedMoment B node5063 node5063Labels := by rfl

def raw35451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35451Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw35451step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35451step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35451step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35451 raw35451Labels = mixedMoment B node5323 node5323Labels := by
  calc
    mixedMoment B raw35451 raw35451Labels = mixedMoment B raw35451step0 raw35451step0Labels := by
      have ha : raw35451step0 = (fun i j => raw35451 (permutation588 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35451step0 raw35451; decide +kernel
      have hl : raw35451step0Labels = raw35451Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35451 raw35451Labels permutation588 permutation2
    mixedMoment B raw35451step0 raw35451step0Labels = mixedMoment B raw35451step1 raw35451step1Labels := by
      have ha : raw35451step1 = -raw35451step0 := by apply Matrix.ext; change ∀ i j, raw35451step1 i j = -(raw35451step0 i j); unfold raw35451step1 raw35451step0; decide +kernel
      have hl : raw35451step1Labels = raw35451step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5323 node5323Labels := by rfl

def raw35452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35452Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35452step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35452step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![-1, 1], ![2, -2], ![2, -2]]
def raw35452step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw35452step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw35452step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw35452step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw35452step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw35452step4 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw35452step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical35452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35452 raw35452Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw35452 raw35452Labels = mixedMoment B raw35452step0 raw35452step0Labels := by
      have hz : ∀ j, raw35452 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35452step0 = (fun i j => raw35452 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35452step0 raw35452; decide +kernel
      have hl : raw35452step0Labels = raw35452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35452 raw35452Labels permutation346 hz
    mixedMoment B raw35452step0 raw35452step0Labels = mixedMoment B raw35452step1 raw35452step1Labels := by
      have hz : ∀ i, raw35452step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw35452step1 = (fun i j => raw35452step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw35452step1 raw35452step0; decide +kernel
      have hl : raw35452step1Labels = (fun j => raw35452step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw35452step0 raw35452step0Labels permutation4 hz
    mixedMoment B raw35452step1 raw35452step1Labels = mixedMoment B raw35452step2 raw35452step2Labels := by
      have ha : raw35452step2 = (fun i j => raw35452step1 (permutation123 i) (permutation0 j)) := by apply Matrix.ext; unfold raw35452step2 raw35452step1; decide +kernel
      have hl : raw35452step2Labels = raw35452step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35452step1 raw35452step1Labels permutation123 permutation0
    mixedMoment B raw35452step2 raw35452step2Labels = mixedMoment B raw35452step3 raw35452step3Labels := by
      have ha : raw35452step3 = -raw35452step2 := by apply Matrix.ext; change ∀ i j, raw35452step3 i j = -(raw35452step2 i j); unfold raw35452step3 raw35452step2; decide +kernel
      have hl : raw35452step3Labels = raw35452step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35452step3 raw35452step3Labels = mixedMoment B raw35452step4 raw35452step4Labels := by
      have ha : raw35452step4 = raw35452step3 := by apply Matrix.ext; unfold raw35452step4 raw35452step3; decide +kernel
      have hl : raw35452step3Labels = labelEmbedding2 ∘ raw35452step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35452step3 raw35452step3Labels raw35452step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw35453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35453Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35453step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35453step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35453step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35453step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35453 raw35453Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw35453 raw35453Labels = mixedMoment B raw35453step0 raw35453step0Labels := by
      have hz : ∀ j, raw35453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35453step0 = (fun i j => raw35453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35453step0 raw35453; decide +kernel
      have hl : raw35453step0Labels = raw35453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35453 raw35453Labels permutation346 hz
    mixedMoment B raw35453step0 raw35453step0Labels = mixedMoment B raw35453step1 raw35453step1Labels := by
      have ha : raw35453step1 = (fun i j => raw35453step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35453step1 raw35453step0; decide +kernel
      have hl : raw35453step1Labels = raw35453step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35453step0 raw35453step0Labels permutation150 permutation7
    mixedMoment B raw35453step1 raw35453step1Labels = mixedMoment B raw35453step2 raw35453step2Labels := by
      have ha : raw35453step2 = raw35453step1 := by apply Matrix.ext; unfold raw35453step2 raw35453step1; decide +kernel
      have hl : raw35453step1Labels = labelEmbedding10 ∘ raw35453step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35453step1 raw35453step1Labels raw35453step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw35454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw35454Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw35454step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35454step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35454step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35454 raw35454Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw35454 raw35454Labels = mixedMoment B raw35454step0 raw35454step0Labels := by
      have hz : ∀ j, raw35454 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35454step0 = (fun i j => raw35454 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35454step0 raw35454; decide +kernel
      have hl : raw35454step0Labels = raw35454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35454 raw35454Labels permutation346 hz
    mixedMoment B raw35454step0 raw35454step0Labels = mixedMoment B raw35454step1 raw35454step1Labels := by
      have ha : raw35454step1 = (fun i j => raw35454step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35454step1 raw35454step0; decide +kernel
      have hl : raw35454step1Labels = raw35454step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35454step0 raw35454step0Labels permutation126 permutation7
    mixedMoment B raw35454step1 raw35454step1Labels = mixedMoment B raw35454step2 raw35454step2Labels := by
      have ha : raw35454step2 = raw35454step1 := by apply Matrix.ext; unfold raw35454step2 raw35454step1; decide +kernel
      have hl : raw35454step1Labels = labelEmbedding10 ∘ raw35454step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35454step1 raw35454step1Labels raw35454step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw35455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35455Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35455step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw35455step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35455step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw35455step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35455 raw35455Labels = mixedMoment B node5193 node5193Labels := by
  calc
    mixedMoment B raw35455 raw35455Labels = mixedMoment B raw35455step0 raw35455step0Labels := by
      have hz : ∀ j, raw35455 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35455step0 = (fun i j => raw35455 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35455step0 raw35455; decide +kernel
      have hl : raw35455step0Labels = raw35455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35455 raw35455Labels permutation346 hz
    mixedMoment B raw35455step0 raw35455step0Labels = mixedMoment B raw35455step1 raw35455step1Labels := by
      have ha : raw35455step1 = (fun i j => raw35455step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35455step1 raw35455step0; decide +kernel
      have hl : raw35455step1Labels = raw35455step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35455step0 raw35455step0Labels permutation32 permutation3
    mixedMoment B raw35455step1 raw35455step1Labels = mixedMoment B raw35455step2 raw35455step2Labels := by
      have ha : raw35455step2 = raw35455step1 := by apply Matrix.ext; unfold raw35455step2 raw35455step1; decide +kernel
      have hl : raw35455step1Labels = labelEmbedding6 ∘ raw35455step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35455step1 raw35455step1Labels raw35455step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5193 node5193Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
