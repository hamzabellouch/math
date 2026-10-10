import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw22272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22272step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22272step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22272step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw22272step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22272step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22272step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22272step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22272step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22272 raw22272Labels = mixedMoment B node4273 node4273Labels := by
  calc
    mixedMoment B raw22272 raw22272Labels = mixedMoment B raw22272step0 raw22272step0Labels := by
      have hz : ∀ j, raw22272 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22272step0 = (fun i j => raw22272 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22272step0 raw22272; decide +kernel
      have hl : raw22272step0Labels = raw22272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22272 raw22272Labels permutation434 hz
    mixedMoment B raw22272step0 raw22272step0Labels = mixedMoment B raw22272step1 raw22272step1Labels := by
      have hz : ∀ j, raw22272step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22272step1 = (fun i j => raw22272step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22272step1 raw22272step0; decide +kernel
      have hl : raw22272step1Labels = raw22272step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22272step0 raw22272step0Labels permutation56 hz
    mixedMoment B raw22272step1 raw22272step1Labels = mixedMoment B raw22272step2 raw22272step2Labels := by
      have ha : raw22272step2 = (fun i j => raw22272step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22272step2 raw22272step1; decide +kernel
      have hl : raw22272step2Labels = raw22272step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22272step1 raw22272step1Labels permutation8 permutation7
    mixedMoment B raw22272step2 raw22272step2Labels = mixedMoment B raw22272step3 raw22272step3Labels := by
      have ha : raw22272step3 = -raw22272step2 := by apply Matrix.ext; change ∀ i j, raw22272step3 i j = -(raw22272step2 i j); unfold raw22272step3 raw22272step2; decide +kernel
      have hl : raw22272step3Labels = raw22272step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22272step3 raw22272step3Labels = mixedMoment B raw22272step4 raw22272step4Labels := by
      have ha : raw22272step4 = raw22272step3 := by apply Matrix.ext; unfold raw22272step4 raw22272step3; decide +kernel
      have hl : raw22272step3Labels = labelEmbedding10 ∘ raw22272step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22272step3 raw22272step3Labels raw22272step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4273 node4273Labels := by rfl

def raw22273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22273step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22273step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22273 raw22273Labels = mixedMoment B node4121 node4121Labels := by
  calc
    mixedMoment B raw22273 raw22273Labels = mixedMoment B raw22273step0 raw22273step0Labels := by
      have hz : ∀ j, raw22273 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22273step0 = (fun i j => raw22273 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22273step0 raw22273; decide +kernel
      have hl : raw22273step0Labels = raw22273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22273 raw22273Labels permutation346 hz
    mixedMoment B raw22273step0 raw22273step0Labels = mixedMoment B raw22273step1 raw22273step1Labels := by
      have hz : ∀ j, raw22273step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22273step1 = (fun i j => raw22273step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22273step1 raw22273step0; decide +kernel
      have hl : raw22273step1Labels = raw22273step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22273step0 raw22273step0Labels permutation56 hz
    _ = mixedMoment B node4121 node4121Labels := by rfl

def raw22274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22274step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22274 raw22274Labels = mixedMoment B node4212 node4212Labels := by
  calc
    mixedMoment B raw22274 raw22274Labels = mixedMoment B raw22274step0 raw22274step0Labels := by
      have hz : ∀ j, raw22274 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22274step0 = (fun i j => raw22274 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22274step0 raw22274; decide +kernel
      have hl : raw22274step0Labels = raw22274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22274 raw22274Labels permutation346 hz
    _ = mixedMoment B node4212 node4212Labels := by rfl

def raw22275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw22275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22275 raw22275Labels = mixedMoment B node4212 node4212Labels := by
  calc
    mixedMoment B raw22275 raw22275Labels = mixedMoment B raw22275step0 raw22275step0Labels := by
      have hz : ∀ j, raw22275 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22275step0 = (fun i j => raw22275 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22275step0 raw22275; decide +kernel
      have hl : raw22275step0Labels = raw22275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22275 raw22275Labels permutation265 hz
    _ = mixedMoment B node4212 node4212Labels := by rfl

def raw22276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22276step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 2, -2], ![3, -1, -2]]
def raw22276step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22276step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw22276step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22276step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22276step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22276step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw22276step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22276 raw22276Labels = mixedMoment B node4272 node4272Labels := by
  calc
    mixedMoment B raw22276 raw22276Labels = mixedMoment B raw22276step0 raw22276step0Labels := by
      have hz : ∀ j, raw22276 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22276step0 = (fun i j => raw22276 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22276step0 raw22276; decide +kernel
      have hl : raw22276step0Labels = raw22276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22276 raw22276Labels permutation346 hz
    mixedMoment B raw22276step0 raw22276step0Labels = mixedMoment B raw22276step1 raw22276step1Labels := by
      have hz : ∀ j, raw22276step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22276step1 = (fun i j => raw22276step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22276step1 raw22276step0; decide +kernel
      have hl : raw22276step1Labels = raw22276step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22276step0 raw22276step0Labels permutation56 hz
    mixedMoment B raw22276step1 raw22276step1Labels = mixedMoment B raw22276step2 raw22276step2Labels := by
      have ha : raw22276step2 = (fun i j => raw22276step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22276step2 raw22276step1; decide +kernel
      have hl : raw22276step2Labels = raw22276step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22276step1 raw22276step1Labels permutation8 permutation7
    mixedMoment B raw22276step2 raw22276step2Labels = mixedMoment B raw22276step3 raw22276step3Labels := by
      have ha : raw22276step3 = -raw22276step2 := by apply Matrix.ext; change ∀ i j, raw22276step3 i j = -(raw22276step2 i j); unfold raw22276step3 raw22276step2; decide +kernel
      have hl : raw22276step3Labels = raw22276step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22276step3 raw22276step3Labels = mixedMoment B raw22276step4 raw22276step4Labels := by
      have ha : raw22276step4 = raw22276step3 := by apply Matrix.ext; unfold raw22276step4 raw22276step3; decide +kernel
      have hl : raw22276step3Labels = labelEmbedding10 ∘ raw22276step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22276step3 raw22276step3Labels raw22276step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4272 node4272Labels := by rfl

def raw22277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22277step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22277step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22277step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw22277step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22277step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22277step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw22277step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw22277step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22277 raw22277Labels = mixedMoment B node4273 node4273Labels := by
  calc
    mixedMoment B raw22277 raw22277Labels = mixedMoment B raw22277step0 raw22277step0Labels := by
      have hz : ∀ j, raw22277 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22277step0 = (fun i j => raw22277 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22277step0 raw22277; decide +kernel
      have hl : raw22277step0Labels = raw22277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22277 raw22277Labels permutation346 hz
    mixedMoment B raw22277step0 raw22277step0Labels = mixedMoment B raw22277step1 raw22277step1Labels := by
      have hz : ∀ j, raw22277step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22277step1 = (fun i j => raw22277step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22277step1 raw22277step0; decide +kernel
      have hl : raw22277step1Labels = raw22277step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22277step0 raw22277step0Labels permutation56 hz
    mixedMoment B raw22277step1 raw22277step1Labels = mixedMoment B raw22277step2 raw22277step2Labels := by
      have ha : raw22277step2 = (fun i j => raw22277step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw22277step2 raw22277step1; decide +kernel
      have hl : raw22277step2Labels = raw22277step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22277step1 raw22277step1Labels permutation8 permutation7
    mixedMoment B raw22277step2 raw22277step2Labels = mixedMoment B raw22277step3 raw22277step3Labels := by
      have ha : raw22277step3 = -raw22277step2 := by apply Matrix.ext; change ∀ i j, raw22277step3 i j = -(raw22277step2 i j); unfold raw22277step3 raw22277step2; decide +kernel
      have hl : raw22277step3Labels = raw22277step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22277step3 raw22277step3Labels = mixedMoment B raw22277step4 raw22277step4Labels := by
      have ha : raw22277step4 = raw22277step3 := by apply Matrix.ext; unfold raw22277step4 raw22277step3; decide +kernel
      have hl : raw22277step3Labels = labelEmbedding10 ∘ raw22277step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22277step3 raw22277step3Labels raw22277step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4273 node4273Labels := by rfl

def raw22278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22278step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22278step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22278step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 0, -2], ![3, -1, -2]]
def raw22278step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22278 raw22278Labels = mixedMoment B node4137 node4137Labels := by
  calc
    mixedMoment B raw22278 raw22278Labels = mixedMoment B raw22278step0 raw22278step0Labels := by
      have hz : ∀ j, raw22278 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22278step0 = (fun i j => raw22278 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22278step0 raw22278; decide +kernel
      have hl : raw22278step0Labels = raw22278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22278 raw22278Labels permutation434 hz
    mixedMoment B raw22278step0 raw22278step0Labels = mixedMoment B raw22278step1 raw22278step1Labels := by
      have hz : ∀ j, raw22278step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22278step1 = (fun i j => raw22278step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22278step1 raw22278step0; decide +kernel
      have hl : raw22278step1Labels = raw22278step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22278step0 raw22278step0Labels permutation80 hz
    mixedMoment B raw22278step1 raw22278step1Labels = mixedMoment B raw22278step2 raw22278step2Labels := by
      have hz : ∀ j, raw22278step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22278step2 = (fun i j => raw22278step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22278step2 raw22278step1; decide +kernel
      have hl : raw22278step2Labels = raw22278step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22278step1 raw22278step1Labels permutation14 hz
    _ = mixedMoment B node4137 node4137Labels := by rfl

def raw22279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22279step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22279 raw22279Labels = mixedMoment B node4228 node4228Labels := by
  calc
    mixedMoment B raw22279 raw22279Labels = mixedMoment B raw22279step0 raw22279step0Labels := by
      have hz : ∀ j, raw22279 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22279step0 = (fun i j => raw22279 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22279step0 raw22279; decide +kernel
      have hl : raw22279step0Labels = raw22279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22279 raw22279Labels permutation434 hz
    mixedMoment B raw22279step0 raw22279step0Labels = mixedMoment B raw22279step1 raw22279step1Labels := by
      have hz : ∀ j, raw22279step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22279step1 = (fun i j => raw22279step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22279step1 raw22279step0; decide +kernel
      have hl : raw22279step1Labels = raw22279step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22279step0 raw22279step0Labels permutation80 hz
    _ = mixedMoment B node4228 node4228Labels := by rfl

def raw22280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22280step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22280 raw22280Labels = mixedMoment B node4228 node4228Labels := by
  calc
    mixedMoment B raw22280 raw22280Labels = mixedMoment B raw22280step0 raw22280step0Labels := by
      have hz : ∀ j, raw22280 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22280step0 = (fun i j => raw22280 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22280step0 raw22280; decide +kernel
      have hl : raw22280step0Labels = raw22280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22280 raw22280Labels permutation434 hz
    mixedMoment B raw22280step0 raw22280step0Labels = mixedMoment B raw22280step1 raw22280step1Labels := by
      have hz : ∀ j, raw22280step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22280step1 = (fun i j => raw22280step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22280step1 raw22280step0; decide +kernel
      have hl : raw22280step1Labels = raw22280step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22280step0 raw22280step0Labels permutation56 hz
    _ = mixedMoment B node4228 node4228Labels := by rfl

def raw22281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22281step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw22281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22281 raw22281Labels = mixedMoment B node4228 node4228Labels := by
  calc
    mixedMoment B raw22281 raw22281Labels = mixedMoment B raw22281step0 raw22281step0Labels := by
      have hz : ∀ j, raw22281 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22281step0 = (fun i j => raw22281 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22281step0 raw22281; decide +kernel
      have hl : raw22281step0Labels = raw22281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22281 raw22281Labels permutation346 hz
    mixedMoment B raw22281step0 raw22281step0Labels = mixedMoment B raw22281step1 raw22281step1Labels := by
      have hz : ∀ j, raw22281step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22281step1 = (fun i j => raw22281step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22281step1 raw22281step0; decide +kernel
      have hl : raw22281step1Labels = raw22281step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22281step0 raw22281step0Labels permutation56 hz
    _ = mixedMoment B node4228 node4228Labels := by rfl

def raw22282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22282step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![2, 0, -2], ![2, 0, -2]]
def raw22282step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22282step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw22282step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw22282step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw22282step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22282 raw22282Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw22282 raw22282Labels = mixedMoment B raw22282step0 raw22282step0Labels := by
      have hz : ∀ j, raw22282 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22282step0 = (fun i j => raw22282 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22282step0 raw22282; decide +kernel
      have hl : raw22282step0Labels = raw22282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22282 raw22282Labels permutation434 hz
    mixedMoment B raw22282step0 raw22282step0Labels = mixedMoment B raw22282step1 raw22282step1Labels := by
      have hz : ∀ j, raw22282step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22282step1 = (fun i j => raw22282step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22282step1 raw22282step0; decide +kernel
      have hl : raw22282step1Labels = raw22282step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22282step0 raw22282step0Labels permutation80 hz
    mixedMoment B raw22282step1 raw22282step1Labels = mixedMoment B raw22282step2 raw22282step2Labels := by
      have hz : ∀ j, raw22282step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22282step2 = (fun i j => raw22282step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22282step2 raw22282step1; decide +kernel
      have hl : raw22282step2Labels = raw22282step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22282step1 raw22282step1Labels permutation14 hz
    mixedMoment B raw22282step2 raw22282step2Labels = mixedMoment B raw22282step3 raw22282step3Labels := by
      have hz : ∀ i, raw22282step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw22282step3 = (fun i j => raw22282step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw22282step3 raw22282step2; decide +kernel
      have hl : raw22282step3Labels = (fun j => raw22282step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22282step2 raw22282step2Labels permutation4 hz
    mixedMoment B raw22282step3 raw22282step3Labels = mixedMoment B raw22282step4 raw22282step4Labels := by
      have ha : raw22282step4 = raw22282step3 := by apply Matrix.ext; unfold raw22282step4 raw22282step3; decide +kernel
      have hl : raw22282step3Labels = labelEmbedding2 ∘ raw22282step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22282step3 raw22282step3Labels raw22282step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4071 node4071Labels := by rfl

def raw22283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22283step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![4, -2, -2]]
def raw22283step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22283 raw22283Labels = mixedMoment B node4134 node4134Labels := by
  calc
    mixedMoment B raw22283 raw22283Labels = mixedMoment B raw22283step0 raw22283step0Labels := by
      have hz : ∀ j, raw22283 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22283step0 = (fun i j => raw22283 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22283step0 raw22283; decide +kernel
      have hl : raw22283step0Labels = raw22283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22283 raw22283Labels permutation434 hz
    mixedMoment B raw22283step0 raw22283step0Labels = mixedMoment B raw22283step1 raw22283step1Labels := by
      have hz : ∀ j, raw22283step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22283step1 = (fun i j => raw22283step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22283step1 raw22283step0; decide +kernel
      have hl : raw22283step1Labels = raw22283step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22283step0 raw22283step0Labels permutation80 hz
    mixedMoment B raw22283step1 raw22283step1Labels = mixedMoment B raw22283step2 raw22283step2Labels := by
      have hz : ∀ j, raw22283step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22283step2 = (fun i j => raw22283step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22283step2 raw22283step1; decide +kernel
      have hl : raw22283step2Labels = raw22283step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22283step1 raw22283step1Labels permutation14 hz
    _ = mixedMoment B node4134 node4134Labels := by rfl

def raw22284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22284step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22284 raw22284Labels = mixedMoment B node4225 node4225Labels := by
  calc
    mixedMoment B raw22284 raw22284Labels = mixedMoment B raw22284step0 raw22284step0Labels := by
      have hz : ∀ j, raw22284 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22284step0 = (fun i j => raw22284 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22284step0 raw22284; decide +kernel
      have hl : raw22284step0Labels = raw22284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22284 raw22284Labels permutation434 hz
    mixedMoment B raw22284step0 raw22284step0Labels = mixedMoment B raw22284step1 raw22284step1Labels := by
      have hz : ∀ j, raw22284step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22284step1 = (fun i j => raw22284step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22284step1 raw22284step0; decide +kernel
      have hl : raw22284step1Labels = raw22284step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22284step0 raw22284step0Labels permutation80 hz
    _ = mixedMoment B node4225 node4225Labels := by rfl

def raw22285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22285step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22285step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22285 raw22285Labels = mixedMoment B node4225 node4225Labels := by
  calc
    mixedMoment B raw22285 raw22285Labels = mixedMoment B raw22285step0 raw22285step0Labels := by
      have hz : ∀ j, raw22285 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22285step0 = (fun i j => raw22285 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22285step0 raw22285; decide +kernel
      have hl : raw22285step0Labels = raw22285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22285 raw22285Labels permutation434 hz
    mixedMoment B raw22285step0 raw22285step0Labels = mixedMoment B raw22285step1 raw22285step1Labels := by
      have hz : ∀ j, raw22285step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22285step1 = (fun i j => raw22285step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22285step1 raw22285step0; decide +kernel
      have hl : raw22285step1Labels = raw22285step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22285step0 raw22285step0Labels permutation56 hz
    _ = mixedMoment B node4225 node4225Labels := by rfl

def raw22286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22286step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw22286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22286 raw22286Labels = mixedMoment B node4225 node4225Labels := by
  calc
    mixedMoment B raw22286 raw22286Labels = mixedMoment B raw22286step0 raw22286step0Labels := by
      have hz : ∀ j, raw22286 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22286step0 = (fun i j => raw22286 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22286step0 raw22286; decide +kernel
      have hl : raw22286step0Labels = raw22286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22286 raw22286Labels permutation346 hz
    mixedMoment B raw22286step0 raw22286step0Labels = mixedMoment B raw22286step1 raw22286step1Labels := by
      have hz : ∀ j, raw22286step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22286step1 = (fun i j => raw22286step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22286step1 raw22286step0; decide +kernel
      have hl : raw22286step1Labels = raw22286step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22286step0 raw22286step0Labels permutation56 hz
    _ = mixedMoment B node4225 node4225Labels := by rfl

def raw22287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -2, -2]]
def raw22287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![4, -2, -2]]
def raw22287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22287step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 2, -2], ![4, -2, -2]]
def raw22287step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22287step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw22287step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22287 raw22287Labels = mixedMoment B node4280 node4280Labels := by
  calc
    mixedMoment B raw22287 raw22287Labels = mixedMoment B raw22287step0 raw22287step0Labels := by
      have hz : ∀ j, raw22287 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22287step0 = (fun i j => raw22287 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22287step0 raw22287; decide +kernel
      have hl : raw22287step0Labels = raw22287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22287 raw22287Labels permutation434 hz
    mixedMoment B raw22287step0 raw22287step0Labels = mixedMoment B raw22287step1 raw22287step1Labels := by
      have hz : ∀ j, raw22287step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22287step1 = (fun i j => raw22287step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22287step1 raw22287step0; decide +kernel
      have hl : raw22287step1Labels = raw22287step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22287step0 raw22287step0Labels permutation80 hz
    mixedMoment B raw22287step1 raw22287step1Labels = mixedMoment B raw22287step2 raw22287step2Labels := by
      have hz : ∀ j, raw22287step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22287step2 = (fun i j => raw22287step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22287step2 raw22287step1; decide +kernel
      have hl : raw22287step2Labels = raw22287step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22287step1 raw22287step1Labels permutation14 hz
    _ = mixedMoment B node4280 node4280Labels := by rfl

def raw22288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22288step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22288step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22288step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22288step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22288step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22288step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22288step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22288step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22288step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22288 raw22288Labels = mixedMoment B node4122 node4122Labels := by
  calc
    mixedMoment B raw22288 raw22288Labels = mixedMoment B raw22288step0 raw22288step0Labels := by
      have hz : ∀ j, raw22288 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22288step0 = (fun i j => raw22288 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22288step0 raw22288; decide +kernel
      have hl : raw22288step0Labels = raw22288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22288 raw22288Labels permutation434 hz
    mixedMoment B raw22288step0 raw22288step0Labels = mixedMoment B raw22288step1 raw22288step1Labels := by
      have hz : ∀ j, raw22288step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22288step1 = (fun i j => raw22288step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22288step1 raw22288step0; decide +kernel
      have hl : raw22288step1Labels = raw22288step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22288step0 raw22288step0Labels permutation56 hz
    mixedMoment B raw22288step1 raw22288step1Labels = mixedMoment B raw22288step2 raw22288step2Labels := by
      have ha : raw22288step2 = (fun i j => raw22288step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22288step2 raw22288step1; decide +kernel
      have hl : raw22288step2Labels = raw22288step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22288step1 raw22288step1Labels permutation8 permutation4
    mixedMoment B raw22288step2 raw22288step2Labels = mixedMoment B raw22288step3 raw22288step3Labels := by
      have ha : raw22288step3 = -raw22288step2 := by apply Matrix.ext; change ∀ i j, raw22288step3 i j = -(raw22288step2 i j); unfold raw22288step3 raw22288step2; decide +kernel
      have hl : raw22288step3Labels = raw22288step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22288step3 raw22288step3Labels = mixedMoment B raw22288step4 raw22288step4Labels := by
      have ha : raw22288step4 = raw22288step3 := by apply Matrix.ext; unfold raw22288step4 raw22288step3; decide +kernel
      have hl : raw22288step3Labels = labelEmbedding7 ∘ raw22288step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22288step3 raw22288step3Labels raw22288step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4122 node4122Labels := by rfl

def raw22289 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22289step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22289step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22289step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22289step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22289step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22289step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22289 raw22289Labels = mixedMoment B node4213 node4213Labels := by
  calc
    mixedMoment B raw22289 raw22289Labels = mixedMoment B raw22289step0 raw22289step0Labels := by
      have hz : ∀ j, raw22289 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22289step0 = (fun i j => raw22289 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22289step0 raw22289; decide +kernel
      have hl : raw22289step0Labels = raw22289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22289 raw22289Labels permutation434 hz
    mixedMoment B raw22289step0 raw22289step0Labels = mixedMoment B raw22289step1 raw22289step1Labels := by
      have ha : raw22289step1 = (fun i j => raw22289step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22289step1 raw22289step0; decide +kernel
      have hl : raw22289step1Labels = raw22289step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22289step0 raw22289step0Labels permutation32 permutation4
    mixedMoment B raw22289step1 raw22289step1Labels = mixedMoment B raw22289step2 raw22289step2Labels := by
      have ha : raw22289step2 = -raw22289step1 := by apply Matrix.ext; change ∀ i j, raw22289step2 i j = -(raw22289step1 i j); unfold raw22289step2 raw22289step1; decide +kernel
      have hl : raw22289step2Labels = raw22289step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22289step2 raw22289step2Labels = mixedMoment B raw22289step3 raw22289step3Labels := by
      have ha : raw22289step3 = raw22289step2 := by apply Matrix.ext; unfold raw22289step3 raw22289step2; decide +kernel
      have hl : raw22289step2Labels = labelEmbedding7 ∘ raw22289step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22289step2 raw22289step2Labels raw22289step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4213 node4213Labels := by rfl

def raw22290 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22290step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22290step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22290step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22290step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22290step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22290 raw22290Labels = mixedMoment B node4213 node4213Labels := by
  calc
    mixedMoment B raw22290 raw22290Labels = mixedMoment B raw22290step0 raw22290step0Labels := by
      have hz : ∀ j, raw22290 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22290step0 = (fun i j => raw22290 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22290step0 raw22290; decide +kernel
      have hl : raw22290step0Labels = raw22290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22290 raw22290Labels permutation265 hz
    mixedMoment B raw22290step0 raw22290step0Labels = mixedMoment B raw22290step1 raw22290step1Labels := by
      have ha : raw22290step1 = (fun i j => raw22290step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22290step1 raw22290step0; decide +kernel
      have hl : raw22290step1Labels = raw22290step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22290step0 raw22290step0Labels permutation38 permutation4
    mixedMoment B raw22290step1 raw22290step1Labels = mixedMoment B raw22290step2 raw22290step2Labels := by
      have ha : raw22290step2 = -raw22290step1 := by apply Matrix.ext; change ∀ i j, raw22290step2 i j = -(raw22290step1 i j); unfold raw22290step2 raw22290step1; decide +kernel
      have hl : raw22290step2Labels = raw22290step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22290step2 raw22290step2Labels = mixedMoment B raw22290step3 raw22290step3Labels := by
      have ha : raw22290step3 = raw22290step2 := by apply Matrix.ext; unfold raw22290step3 raw22290step2; decide +kernel
      have hl : raw22290step2Labels = labelEmbedding7 ∘ raw22290step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22290step2 raw22290step2Labels raw22290step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4213 node4213Labels := by rfl

def raw22291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22291step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22291step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22291step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22291step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22291step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22291step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22291step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22291step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22291 raw22291Labels = mixedMoment B node4122 node4122Labels := by
  calc
    mixedMoment B raw22291 raw22291Labels = mixedMoment B raw22291step0 raw22291step0Labels := by
      have hz : ∀ j, raw22291 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22291step0 = (fun i j => raw22291 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22291step0 raw22291; decide +kernel
      have hl : raw22291step0Labels = raw22291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22291 raw22291Labels permutation346 hz
    mixedMoment B raw22291step0 raw22291step0Labels = mixedMoment B raw22291step1 raw22291step1Labels := by
      have hz : ∀ j, raw22291step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22291step1 = (fun i j => raw22291step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22291step1 raw22291step0; decide +kernel
      have hl : raw22291step1Labels = raw22291step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22291step0 raw22291step0Labels permutation56 hz
    mixedMoment B raw22291step1 raw22291step1Labels = mixedMoment B raw22291step2 raw22291step2Labels := by
      have ha : raw22291step2 = (fun i j => raw22291step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22291step2 raw22291step1; decide +kernel
      have hl : raw22291step2Labels = raw22291step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22291step1 raw22291step1Labels permutation8 permutation4
    mixedMoment B raw22291step2 raw22291step2Labels = mixedMoment B raw22291step3 raw22291step3Labels := by
      have ha : raw22291step3 = -raw22291step2 := by apply Matrix.ext; change ∀ i j, raw22291step3 i j = -(raw22291step2 i j); unfold raw22291step3 raw22291step2; decide +kernel
      have hl : raw22291step3Labels = raw22291step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22291step3 raw22291step3Labels = mixedMoment B raw22291step4 raw22291step4Labels := by
      have ha : raw22291step4 = raw22291step3 := by apply Matrix.ext; unfold raw22291step4 raw22291step3; decide +kernel
      have hl : raw22291step3Labels = labelEmbedding7 ∘ raw22291step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22291step3 raw22291step3Labels raw22291step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4122 node4122Labels := by rfl

def raw22292 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22292step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22292step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22292step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22292step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22292 raw22292Labels = mixedMoment B node4213 node4213Labels := by
  calc
    mixedMoment B raw22292 raw22292Labels = mixedMoment B raw22292step0 raw22292step0Labels := by
      have hz : ∀ j, raw22292 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22292step0 = (fun i j => raw22292 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22292step0 raw22292; decide +kernel
      have hl : raw22292step0Labels = raw22292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22292 raw22292Labels permutation346 hz
    mixedMoment B raw22292step0 raw22292step0Labels = mixedMoment B raw22292step1 raw22292step1Labels := by
      have ha : raw22292step1 = (fun i j => raw22292step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22292step1 raw22292step0; decide +kernel
      have hl : raw22292step1Labels = raw22292step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22292step0 raw22292step0Labels permutation32 permutation4
    mixedMoment B raw22292step1 raw22292step1Labels = mixedMoment B raw22292step2 raw22292step2Labels := by
      have ha : raw22292step2 = -raw22292step1 := by apply Matrix.ext; change ∀ i j, raw22292step2 i j = -(raw22292step1 i j); unfold raw22292step2 raw22292step1; decide +kernel
      have hl : raw22292step2Labels = raw22292step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22292step2 raw22292step2Labels = mixedMoment B raw22292step3 raw22292step3Labels := by
      have ha : raw22292step3 = raw22292step2 := by apply Matrix.ext; unfold raw22292step3 raw22292step2; decide +kernel
      have hl : raw22292step2Labels = labelEmbedding7 ∘ raw22292step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22292step2 raw22292step2Labels raw22292step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4213 node4213Labels := by rfl

def raw22293 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw22293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw22293step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22293step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22293step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw22293step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22293 raw22293Labels = mixedMoment B node4213 node4213Labels := by
  calc
    mixedMoment B raw22293 raw22293Labels = mixedMoment B raw22293step0 raw22293step0Labels := by
      have hz : ∀ j, raw22293 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22293step0 = (fun i j => raw22293 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22293step0 raw22293; decide +kernel
      have hl : raw22293step0Labels = raw22293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22293 raw22293Labels permutation265 hz
    mixedMoment B raw22293step0 raw22293step0Labels = mixedMoment B raw22293step1 raw22293step1Labels := by
      have ha : raw22293step1 = (fun i j => raw22293step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22293step1 raw22293step0; decide +kernel
      have hl : raw22293step1Labels = raw22293step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22293step0 raw22293step0Labels permutation32 permutation4
    mixedMoment B raw22293step1 raw22293step1Labels = mixedMoment B raw22293step2 raw22293step2Labels := by
      have ha : raw22293step2 = -raw22293step1 := by apply Matrix.ext; change ∀ i j, raw22293step2 i j = -(raw22293step1 i j); unfold raw22293step2 raw22293step1; decide +kernel
      have hl : raw22293step2Labels = raw22293step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22293step2 raw22293step2Labels = mixedMoment B raw22293step3 raw22293step3Labels := by
      have ha : raw22293step3 = raw22293step2 := by apply Matrix.ext; unfold raw22293step3 raw22293step2; decide +kernel
      have hl : raw22293step2Labels = labelEmbedding7 ∘ raw22293step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22293step2 raw22293step2Labels raw22293step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4213 node4213Labels := by rfl

def raw22294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22294step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22294step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22294step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -3, 1], ![-1, -2, 3]]
def raw22294step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22294step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![-2, -1, 3], ![-3, 2, 1]]
def raw22294step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22294step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]
def raw22294step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22294step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 1, -3], ![3, -2, -1]]
def raw22294step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22294 raw22294Labels = mixedMoment B node4138 node4138Labels := by
  calc
    mixedMoment B raw22294 raw22294Labels = mixedMoment B raw22294step0 raw22294step0Labels := by
      have hz : ∀ j, raw22294 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22294step0 = (fun i j => raw22294 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22294step0 raw22294; decide +kernel
      have hl : raw22294step0Labels = raw22294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22294 raw22294Labels permutation434 hz
    mixedMoment B raw22294step0 raw22294step0Labels = mixedMoment B raw22294step1 raw22294step1Labels := by
      have hz : ∀ j, raw22294step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22294step1 = (fun i j => raw22294step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22294step1 raw22294step0; decide +kernel
      have hl : raw22294step1Labels = raw22294step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22294step0 raw22294step0Labels permutation80 hz
    mixedMoment B raw22294step1 raw22294step1Labels = mixedMoment B raw22294step2 raw22294step2Labels := by
      have hz : ∀ j, raw22294step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22294step2 = (fun i j => raw22294step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22294step2 raw22294step1; decide +kernel
      have hl : raw22294step2Labels = raw22294step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22294step1 raw22294step1Labels permutation14 hz
    mixedMoment B raw22294step2 raw22294step2Labels = mixedMoment B raw22294step3 raw22294step3Labels := by
      have ha : raw22294step3 = (fun i j => raw22294step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22294step3 raw22294step2; decide +kernel
      have hl : raw22294step3Labels = raw22294step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22294step2 raw22294step2Labels permutation3 permutation4
    mixedMoment B raw22294step3 raw22294step3Labels = mixedMoment B raw22294step4 raw22294step4Labels := by
      have ha : raw22294step4 = -raw22294step3 := by apply Matrix.ext; change ∀ i j, raw22294step4 i j = -(raw22294step3 i j); unfold raw22294step4 raw22294step3; decide +kernel
      have hl : raw22294step4Labels = raw22294step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22294step4 raw22294step4Labels = mixedMoment B raw22294step5 raw22294step5Labels := by
      have ha : raw22294step5 = raw22294step4 := by apply Matrix.ext; unfold raw22294step5 raw22294step4; decide +kernel
      have hl : raw22294step4Labels = labelEmbedding7 ∘ raw22294step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22294step4 raw22294step4Labels raw22294step5Labels labelEmbedding7 hl
    _ = mixedMoment B node4138 node4138Labels := by rfl

def raw22295 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22295step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22295step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22295step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22295step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, -1, 3], ![-3, 2, 1]]
def raw22295step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22295step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22295step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22295step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22295step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22295 raw22295Labels = mixedMoment B node4229 node4229Labels := by
  calc
    mixedMoment B raw22295 raw22295Labels = mixedMoment B raw22295step0 raw22295step0Labels := by
      have hz : ∀ j, raw22295 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22295step0 = (fun i j => raw22295 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22295step0 raw22295; decide +kernel
      have hl : raw22295step0Labels = raw22295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22295 raw22295Labels permutation434 hz
    mixedMoment B raw22295step0 raw22295step0Labels = mixedMoment B raw22295step1 raw22295step1Labels := by
      have hz : ∀ j, raw22295step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22295step1 = (fun i j => raw22295step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22295step1 raw22295step0; decide +kernel
      have hl : raw22295step1Labels = raw22295step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22295step0 raw22295step0Labels permutation80 hz
    mixedMoment B raw22295step1 raw22295step1Labels = mixedMoment B raw22295step2 raw22295step2Labels := by
      have ha : raw22295step2 = (fun i j => raw22295step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22295step2 raw22295step1; decide +kernel
      have hl : raw22295step2Labels = raw22295step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22295step1 raw22295step1Labels permutation9 permutation4
    mixedMoment B raw22295step2 raw22295step2Labels = mixedMoment B raw22295step3 raw22295step3Labels := by
      have ha : raw22295step3 = -raw22295step2 := by apply Matrix.ext; change ∀ i j, raw22295step3 i j = -(raw22295step2 i j); unfold raw22295step3 raw22295step2; decide +kernel
      have hl : raw22295step3Labels = raw22295step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22295step3 raw22295step3Labels = mixedMoment B raw22295step4 raw22295step4Labels := by
      have ha : raw22295step4 = raw22295step3 := by apply Matrix.ext; unfold raw22295step4 raw22295step3; decide +kernel
      have hl : raw22295step3Labels = labelEmbedding7 ∘ raw22295step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22295step3 raw22295step3Labels raw22295step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4229 node4229Labels := by rfl

def raw22296 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22296step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22296step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22296step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, -1, 3], ![-3, 2, 1]]
def raw22296step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22296step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22296step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22296step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22296step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22296 raw22296Labels = mixedMoment B node4229 node4229Labels := by
  calc
    mixedMoment B raw22296 raw22296Labels = mixedMoment B raw22296step0 raw22296step0Labels := by
      have hz : ∀ j, raw22296 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22296step0 = (fun i j => raw22296 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22296step0 raw22296; decide +kernel
      have hl : raw22296step0Labels = raw22296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22296 raw22296Labels permutation434 hz
    mixedMoment B raw22296step0 raw22296step0Labels = mixedMoment B raw22296step1 raw22296step1Labels := by
      have hz : ∀ j, raw22296step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22296step1 = (fun i j => raw22296step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22296step1 raw22296step0; decide +kernel
      have hl : raw22296step1Labels = raw22296step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22296step0 raw22296step0Labels permutation56 hz
    mixedMoment B raw22296step1 raw22296step1Labels = mixedMoment B raw22296step2 raw22296step2Labels := by
      have ha : raw22296step2 = (fun i j => raw22296step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22296step2 raw22296step1; decide +kernel
      have hl : raw22296step2Labels = raw22296step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22296step1 raw22296step1Labels permutation9 permutation4
    mixedMoment B raw22296step2 raw22296step2Labels = mixedMoment B raw22296step3 raw22296step3Labels := by
      have ha : raw22296step3 = -raw22296step2 := by apply Matrix.ext; change ∀ i j, raw22296step3 i j = -(raw22296step2 i j); unfold raw22296step3 raw22296step2; decide +kernel
      have hl : raw22296step3Labels = raw22296step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22296step3 raw22296step3Labels = mixedMoment B raw22296step4 raw22296step4Labels := by
      have ha : raw22296step4 = raw22296step3 := by apply Matrix.ext; unfold raw22296step4 raw22296step3; decide +kernel
      have hl : raw22296step3Labels = labelEmbedding7 ∘ raw22296step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22296step3 raw22296step3Labels raw22296step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4229 node4229Labels := by rfl

def raw22297 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw22297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, -1, 3], ![-3, 2, 1]]
def raw22297step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22297step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22297step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22297step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw22297step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22297 raw22297Labels = mixedMoment B node4229 node4229Labels := by
  calc
    mixedMoment B raw22297 raw22297Labels = mixedMoment B raw22297step0 raw22297step0Labels := by
      have hz : ∀ j, raw22297 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22297step0 = (fun i j => raw22297 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22297step0 raw22297; decide +kernel
      have hl : raw22297step0Labels = raw22297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22297 raw22297Labels permutation346 hz
    mixedMoment B raw22297step0 raw22297step0Labels = mixedMoment B raw22297step1 raw22297step1Labels := by
      have hz : ∀ j, raw22297step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22297step1 = (fun i j => raw22297step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22297step1 raw22297step0; decide +kernel
      have hl : raw22297step1Labels = raw22297step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22297step0 raw22297step0Labels permutation56 hz
    mixedMoment B raw22297step1 raw22297step1Labels = mixedMoment B raw22297step2 raw22297step2Labels := by
      have ha : raw22297step2 = (fun i j => raw22297step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22297step2 raw22297step1; decide +kernel
      have hl : raw22297step2Labels = raw22297step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22297step1 raw22297step1Labels permutation9 permutation4
    mixedMoment B raw22297step2 raw22297step2Labels = mixedMoment B raw22297step3 raw22297step3Labels := by
      have ha : raw22297step3 = -raw22297step2 := by apply Matrix.ext; change ∀ i j, raw22297step3 i j = -(raw22297step2 i j); unfold raw22297step3 raw22297step2; decide +kernel
      have hl : raw22297step3Labels = raw22297step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22297step3 raw22297step3Labels = mixedMoment B raw22297step4 raw22297step4Labels := by
      have ha : raw22297step4 = raw22297step3 := by apply Matrix.ext; unfold raw22297step4 raw22297step3; decide +kernel
      have hl : raw22297step3Labels = labelEmbedding7 ∘ raw22297step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22297step3 raw22297step3Labels raw22297step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4229 node4229Labels := by rfl

def raw22298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 5, -4], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22298step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22298step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -2, 1], ![0, -3, 3]]
def raw22298step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22298step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![5, -1, -4], ![-2, 1, 1], ![-3, 0, 3]]
def raw22298step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22298step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, -1, -1], ![3, 0, -3]]
def raw22298step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22298step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 1, 4], ![2, -1, -1], ![3, 0, -3]]
def raw22298step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22298 raw22298Labels = mixedMoment B node4136 node4136Labels := by
  calc
    mixedMoment B raw22298 raw22298Labels = mixedMoment B raw22298step0 raw22298step0Labels := by
      have hz : ∀ j, raw22298 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22298step0 = (fun i j => raw22298 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22298step0 raw22298; decide +kernel
      have hl : raw22298step0Labels = raw22298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22298 raw22298Labels permutation434 hz
    mixedMoment B raw22298step0 raw22298step0Labels = mixedMoment B raw22298step1 raw22298step1Labels := by
      have hz : ∀ j, raw22298step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22298step1 = (fun i j => raw22298step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22298step1 raw22298step0; decide +kernel
      have hl : raw22298step1Labels = raw22298step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22298step0 raw22298step0Labels permutation80 hz
    mixedMoment B raw22298step1 raw22298step1Labels = mixedMoment B raw22298step2 raw22298step2Labels := by
      have hz : ∀ j, raw22298step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22298step2 = (fun i j => raw22298step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22298step2 raw22298step1; decide +kernel
      have hl : raw22298step2Labels = raw22298step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22298step1 raw22298step1Labels permutation14 hz
    mixedMoment B raw22298step2 raw22298step2Labels = mixedMoment B raw22298step3 raw22298step3Labels := by
      have ha : raw22298step3 = (fun i j => raw22298step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22298step3 raw22298step2; decide +kernel
      have hl : raw22298step3Labels = raw22298step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22298step2 raw22298step2Labels permutation2 permutation4
    mixedMoment B raw22298step3 raw22298step3Labels = mixedMoment B raw22298step4 raw22298step4Labels := by
      have ha : raw22298step4 = -raw22298step3 := by apply Matrix.ext; change ∀ i j, raw22298step4 i j = -(raw22298step3 i j); unfold raw22298step4 raw22298step3; decide +kernel
      have hl : raw22298step4Labels = raw22298step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22298step4 raw22298step4Labels = mixedMoment B raw22298step5 raw22298step5Labels := by
      have ha : raw22298step5 = raw22298step4 := by apply Matrix.ext; unfold raw22298step5 raw22298step4; decide +kernel
      have hl : raw22298step4Labels = labelEmbedding7 ∘ raw22298step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22298step4 raw22298step4Labels raw22298step5Labels labelEmbedding7 hl
    _ = mixedMoment B node4136 node4136Labels := by rfl

def raw22299 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22299step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22299step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22299step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, 1, 1], ![-3, 0, 3]]
def raw22299step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22299step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw22299step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22299step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw22299step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22299 raw22299Labels = mixedMoment B node4227 node4227Labels := by
  calc
    mixedMoment B raw22299 raw22299Labels = mixedMoment B raw22299step0 raw22299step0Labels := by
      have hz : ∀ j, raw22299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22299step0 = (fun i j => raw22299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22299step0 raw22299; decide +kernel
      have hl : raw22299step0Labels = raw22299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22299 raw22299Labels permutation434 hz
    mixedMoment B raw22299step0 raw22299step0Labels = mixedMoment B raw22299step1 raw22299step1Labels := by
      have hz : ∀ j, raw22299step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22299step1 = (fun i j => raw22299step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22299step1 raw22299step0; decide +kernel
      have hl : raw22299step1Labels = raw22299step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22299step0 raw22299step0Labels permutation80 hz
    mixedMoment B raw22299step1 raw22299step1Labels = mixedMoment B raw22299step2 raw22299step2Labels := by
      have ha : raw22299step2 = (fun i j => raw22299step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22299step2 raw22299step1; decide +kernel
      have hl : raw22299step2Labels = raw22299step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22299step1 raw22299step1Labels permutation8 permutation4
    mixedMoment B raw22299step2 raw22299step2Labels = mixedMoment B raw22299step3 raw22299step3Labels := by
      have ha : raw22299step3 = -raw22299step2 := by apply Matrix.ext; change ∀ i j, raw22299step3 i j = -(raw22299step2 i j); unfold raw22299step3 raw22299step2; decide +kernel
      have hl : raw22299step3Labels = raw22299step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22299step3 raw22299step3Labels = mixedMoment B raw22299step4 raw22299step4Labels := by
      have ha : raw22299step4 = raw22299step3 := by apply Matrix.ext; unfold raw22299step4 raw22299step3; decide +kernel
      have hl : raw22299step3Labels = labelEmbedding7 ∘ raw22299step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22299step3 raw22299step3Labels raw22299step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4227 node4227Labels := by rfl

def raw22300 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22300step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22300step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw22300step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22300step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, 1, 1], ![-3, 0, 3]]
def raw22300step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22300step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw22300step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22300step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw22300step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22300 raw22300Labels = mixedMoment B node4227 node4227Labels := by
  calc
    mixedMoment B raw22300 raw22300Labels = mixedMoment B raw22300step0 raw22300step0Labels := by
      have hz : ∀ j, raw22300 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22300step0 = (fun i j => raw22300 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22300step0 raw22300; decide +kernel
      have hl : raw22300step0Labels = raw22300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22300 raw22300Labels permutation434 hz
    mixedMoment B raw22300step0 raw22300step0Labels = mixedMoment B raw22300step1 raw22300step1Labels := by
      have hz : ∀ j, raw22300step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22300step1 = (fun i j => raw22300step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22300step1 raw22300step0; decide +kernel
      have hl : raw22300step1Labels = raw22300step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22300step0 raw22300step0Labels permutation56 hz
    mixedMoment B raw22300step1 raw22300step1Labels = mixedMoment B raw22300step2 raw22300step2Labels := by
      have ha : raw22300step2 = (fun i j => raw22300step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22300step2 raw22300step1; decide +kernel
      have hl : raw22300step2Labels = raw22300step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22300step1 raw22300step1Labels permutation8 permutation4
    mixedMoment B raw22300step2 raw22300step2Labels = mixedMoment B raw22300step3 raw22300step3Labels := by
      have ha : raw22300step3 = -raw22300step2 := by apply Matrix.ext; change ∀ i j, raw22300step3 i j = -(raw22300step2 i j); unfold raw22300step3 raw22300step2; decide +kernel
      have hl : raw22300step3Labels = raw22300step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw22300step3 raw22300step3Labels = mixedMoment B raw22300step4 raw22300step4Labels := by
      have ha : raw22300step4 = raw22300step3 := by apply Matrix.ext; unfold raw22300step4 raw22300step3; decide +kernel
      have hl : raw22300step3Labels = labelEmbedding7 ∘ raw22300step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22300step3 raw22300step3Labels raw22300step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4227 node4227Labels := by rfl

def raw22301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22301step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22301step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![3, -3]]
def raw22301step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22301 raw22301Labels = mixedMoment B node4058 node4058Labels := by
  calc
    mixedMoment B raw22301 raw22301Labels = mixedMoment B raw22301step0 raw22301step0Labels := by
      have hz : ∀ j, raw22301 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22301step0 = (fun i j => raw22301 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22301step0 raw22301; decide +kernel
      have hl : raw22301step0Labels = raw22301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22301 raw22301Labels permutation434 hz
    mixedMoment B raw22301step0 raw22301step0Labels = mixedMoment B raw22301step1 raw22301step1Labels := by
      have hz : ∀ j, raw22301step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22301step1 = (fun i j => raw22301step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22301step1 raw22301step0; decide +kernel
      have hl : raw22301step1Labels = raw22301step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22301step0 raw22301step0Labels permutation80 hz
    mixedMoment B raw22301step1 raw22301step1Labels = mixedMoment B raw22301step2 raw22301step2Labels := by
      have hz : ∀ i, raw22301step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22301step2 = (fun i j => raw22301step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22301step2 raw22301step1; decide +kernel
      have hl : raw22301step2Labels = (fun j => raw22301step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22301step1 raw22301step1Labels permutation6 hz
    _ = mixedMoment B node4058 node4058Labels := by rfl

def raw22302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22302step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22302step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![1, -1], ![3, -3]]
def raw22302step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22302step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw22302step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22302 raw22302Labels = mixedMoment B node4064 node4064Labels := by
  calc
    mixedMoment B raw22302 raw22302Labels = mixedMoment B raw22302step0 raw22302step0Labels := by
      have hz : ∀ j, raw22302 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22302step0 = (fun i j => raw22302 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22302step0 raw22302; decide +kernel
      have hl : raw22302step0Labels = raw22302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22302 raw22302Labels permutation434 hz
    mixedMoment B raw22302step0 raw22302step0Labels = mixedMoment B raw22302step1 raw22302step1Labels := by
      have hz : ∀ i, raw22302step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22302step1 = (fun i j => raw22302step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22302step1 raw22302step0; decide +kernel
      have hl : raw22302step1Labels = (fun j => raw22302step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22302step0 raw22302step0Labels permutation6 hz
    mixedMoment B raw22302step1 raw22302step1Labels = mixedMoment B raw22302step2 raw22302step2Labels := by
      have ha : raw22302step2 = (fun i j => raw22302step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22302step2 raw22302step1; decide +kernel
      have hl : raw22302step2Labels = raw22302step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22302step1 raw22302step1Labels permutation38 permutation0
    _ = mixedMoment B node4064 node4064Labels := by rfl

def raw22303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22303step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22303step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![1, -1], ![3, -3]]
def raw22303step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22303step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw22303step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22303 raw22303Labels = mixedMoment B node4064 node4064Labels := by
  calc
    mixedMoment B raw22303 raw22303Labels = mixedMoment B raw22303step0 raw22303step0Labels := by
      have hz : ∀ j, raw22303 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22303step0 = (fun i j => raw22303 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22303step0 raw22303; decide +kernel
      have hl : raw22303step0Labels = raw22303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22303 raw22303Labels permutation346 hz
    mixedMoment B raw22303step0 raw22303step0Labels = mixedMoment B raw22303step1 raw22303step1Labels := by
      have hz : ∀ i, raw22303step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22303step1 = (fun i j => raw22303step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22303step1 raw22303step0; decide +kernel
      have hl : raw22303step1Labels = (fun j => raw22303step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22303step0 raw22303step0Labels permutation6 hz
    mixedMoment B raw22303step1 raw22303step1Labels = mixedMoment B raw22303step2 raw22303step2Labels := by
      have ha : raw22303step2 = (fun i j => raw22303step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22303step2 raw22303step1; decide +kernel
      have hl : raw22303step2Labels = raw22303step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22303step1 raw22303step1Labels permutation38 permutation0
    _ = mixedMoment B node4064 node4064Labels := by rfl

def raw22304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22304Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22304step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22304step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22304step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![3, -3]]
def raw22304step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22304 raw22304Labels = mixedMoment B node4058 node4058Labels := by
  calc
    mixedMoment B raw22304 raw22304Labels = mixedMoment B raw22304step0 raw22304step0Labels := by
      have hz : ∀ j, raw22304 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22304step0 = (fun i j => raw22304 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22304step0 raw22304; decide +kernel
      have hl : raw22304step0Labels = raw22304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22304 raw22304Labels permutation434 hz
    mixedMoment B raw22304step0 raw22304step0Labels = mixedMoment B raw22304step1 raw22304step1Labels := by
      have hz : ∀ j, raw22304step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22304step1 = (fun i j => raw22304step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22304step1 raw22304step0; decide +kernel
      have hl : raw22304step1Labels = raw22304step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22304step0 raw22304step0Labels permutation56 hz
    mixedMoment B raw22304step1 raw22304step1Labels = mixedMoment B raw22304step2 raw22304step2Labels := by
      have hz : ∀ i, raw22304step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22304step2 = (fun i j => raw22304step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22304step2 raw22304step1; decide +kernel
      have hl : raw22304step2Labels = (fun j => raw22304step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22304step1 raw22304step1Labels permutation6 hz
    _ = mixedMoment B node4058 node4058Labels := by rfl

def raw22305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22305Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22305step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22305step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw22305step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22305 raw22305Labels = mixedMoment B node4064 node4064Labels := by
  calc
    mixedMoment B raw22305 raw22305Labels = mixedMoment B raw22305step0 raw22305step0Labels := by
      have hz : ∀ j, raw22305 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22305step0 = (fun i j => raw22305 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22305step0 raw22305; decide +kernel
      have hl : raw22305step0Labels = raw22305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22305 raw22305Labels permutation434 hz
    mixedMoment B raw22305step0 raw22305step0Labels = mixedMoment B raw22305step1 raw22305step1Labels := by
      have hz : ∀ i, raw22305step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22305step1 = (fun i j => raw22305step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22305step1 raw22305step0; decide +kernel
      have hl : raw22305step1Labels = (fun j => raw22305step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22305step0 raw22305step0Labels permutation6 hz
    _ = mixedMoment B node4064 node4064Labels := by rfl

def raw22306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22306Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22306step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22306step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![1, -1], ![3, -3]]
def raw22306step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22306step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw22306step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22306 raw22306Labels = mixedMoment B node4064 node4064Labels := by
  calc
    mixedMoment B raw22306 raw22306Labels = mixedMoment B raw22306step0 raw22306step0Labels := by
      have hz : ∀ j, raw22306 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22306step0 = (fun i j => raw22306 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22306step0 raw22306; decide +kernel
      have hl : raw22306step0Labels = raw22306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22306 raw22306Labels permutation265 hz
    mixedMoment B raw22306step0 raw22306step0Labels = mixedMoment B raw22306step1 raw22306step1Labels := by
      have hz : ∀ i, raw22306step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22306step1 = (fun i j => raw22306step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22306step1 raw22306step0; decide +kernel
      have hl : raw22306step1Labels = (fun j => raw22306step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22306step0 raw22306step0Labels permutation6 hz
    mixedMoment B raw22306step1 raw22306step1Labels = mixedMoment B raw22306step2 raw22306step2Labels := by
      have ha : raw22306step2 = (fun i j => raw22306step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22306step2 raw22306step1; decide +kernel
      have hl : raw22306step2Labels = raw22306step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22306step1 raw22306step1Labels permutation38 permutation0
    _ = mixedMoment B node4064 node4064Labels := by rfl

def raw22307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22307Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22307step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22307step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22307step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22307step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![3, -3]]
def raw22307step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22307 raw22307Labels = mixedMoment B node4058 node4058Labels := by
  calc
    mixedMoment B raw22307 raw22307Labels = mixedMoment B raw22307step0 raw22307step0Labels := by
      have hz : ∀ j, raw22307 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22307step0 = (fun i j => raw22307 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22307step0 raw22307; decide +kernel
      have hl : raw22307step0Labels = raw22307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22307 raw22307Labels permutation346 hz
    mixedMoment B raw22307step0 raw22307step0Labels = mixedMoment B raw22307step1 raw22307step1Labels := by
      have hz : ∀ j, raw22307step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22307step1 = (fun i j => raw22307step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22307step1 raw22307step0; decide +kernel
      have hl : raw22307step1Labels = raw22307step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22307step0 raw22307step0Labels permutation56 hz
    mixedMoment B raw22307step1 raw22307step1Labels = mixedMoment B raw22307step2 raw22307step2Labels := by
      have hz : ∀ i, raw22307step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22307step2 = (fun i j => raw22307step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22307step2 raw22307step1; decide +kernel
      have hl : raw22307step2Labels = (fun j => raw22307step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22307step1 raw22307step1Labels permutation6 hz
    _ = mixedMoment B node4058 node4058Labels := by rfl

def raw22308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22308Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22308step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22308step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw22308step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22308 raw22308Labels = mixedMoment B node4064 node4064Labels := by
  calc
    mixedMoment B raw22308 raw22308Labels = mixedMoment B raw22308step0 raw22308step0Labels := by
      have hz : ∀ j, raw22308 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22308step0 = (fun i j => raw22308 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22308step0 raw22308; decide +kernel
      have hl : raw22308step0Labels = raw22308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22308 raw22308Labels permutation346 hz
    mixedMoment B raw22308step0 raw22308step0Labels = mixedMoment B raw22308step1 raw22308step1Labels := by
      have hz : ∀ i, raw22308step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22308step1 = (fun i j => raw22308step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22308step1 raw22308step0; decide +kernel
      have hl : raw22308step1Labels = (fun j => raw22308step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22308step0 raw22308step0Labels permutation6 hz
    _ = mixedMoment B node4064 node4064Labels := by rfl

def raw22309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22309Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw22309step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22309step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw22309step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22309 raw22309Labels = mixedMoment B node4064 node4064Labels := by
  calc
    mixedMoment B raw22309 raw22309Labels = mixedMoment B raw22309step0 raw22309step0Labels := by
      have hz : ∀ j, raw22309 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22309step0 = (fun i j => raw22309 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22309step0 raw22309; decide +kernel
      have hl : raw22309step0Labels = raw22309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22309 raw22309Labels permutation265 hz
    mixedMoment B raw22309step0 raw22309step0Labels = mixedMoment B raw22309step1 raw22309step1Labels := by
      have hz : ∀ i, raw22309step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22309step1 = (fun i j => raw22309step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22309step1 raw22309step0; decide +kernel
      have hl : raw22309step1Labels = (fun j => raw22309step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22309step0 raw22309step0Labels permutation6 hz
    _ = mixedMoment B node4064 node4064Labels := by rfl

def raw22310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22310Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22310step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22310step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22310step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22310step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 5, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22310step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22310step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![3, -3]]
def raw22310step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22310 raw22310Labels = mixedMoment B node4061 node4061Labels := by
  calc
    mixedMoment B raw22310 raw22310Labels = mixedMoment B raw22310step0 raw22310step0Labels := by
      have hz : ∀ j, raw22310 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22310step0 = (fun i j => raw22310 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22310step0 raw22310; decide +kernel
      have hl : raw22310step0Labels = raw22310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22310 raw22310Labels permutation434 hz
    mixedMoment B raw22310step0 raw22310step0Labels = mixedMoment B raw22310step1 raw22310step1Labels := by
      have hz : ∀ j, raw22310step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22310step1 = (fun i j => raw22310step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22310step1 raw22310step0; decide +kernel
      have hl : raw22310step1Labels = raw22310step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22310step0 raw22310step0Labels permutation80 hz
    mixedMoment B raw22310step1 raw22310step1Labels = mixedMoment B raw22310step2 raw22310step2Labels := by
      have hz : ∀ j, raw22310step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22310step2 = (fun i j => raw22310step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22310step2 raw22310step1; decide +kernel
      have hl : raw22310step2Labels = raw22310step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22310step1 raw22310step1Labels permutation14 hz
    mixedMoment B raw22310step2 raw22310step2Labels = mixedMoment B raw22310step3 raw22310step3Labels := by
      have hz : ∀ i, raw22310step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22310step3 = (fun i j => raw22310step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22310step3 raw22310step2; decide +kernel
      have hl : raw22310step3Labels = (fun j => raw22310step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22310step2 raw22310step2Labels permutation6 hz
    _ = mixedMoment B node4061 node4061Labels := by rfl

def raw22311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22311Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22311step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22311step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22311step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22311step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def raw22311step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22311 raw22311Labels = mixedMoment B node4067 node4067Labels := by
  calc
    mixedMoment B raw22311 raw22311Labels = mixedMoment B raw22311step0 raw22311step0Labels := by
      have hz : ∀ j, raw22311 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22311step0 = (fun i j => raw22311 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22311step0 raw22311; decide +kernel
      have hl : raw22311step0Labels = raw22311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22311 raw22311Labels permutation434 hz
    mixedMoment B raw22311step0 raw22311step0Labels = mixedMoment B raw22311step1 raw22311step1Labels := by
      have hz : ∀ j, raw22311step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22311step1 = (fun i j => raw22311step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22311step1 raw22311step0; decide +kernel
      have hl : raw22311step1Labels = raw22311step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22311step0 raw22311step0Labels permutation80 hz
    mixedMoment B raw22311step1 raw22311step1Labels = mixedMoment B raw22311step2 raw22311step2Labels := by
      have hz : ∀ i, raw22311step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22311step2 = (fun i j => raw22311step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22311step2 raw22311step1; decide +kernel
      have hl : raw22311step2Labels = (fun j => raw22311step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22311step1 raw22311step1Labels permutation6 hz
    _ = mixedMoment B node4067 node4067Labels := by rfl

def raw22312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22312Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22312step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22312step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22312step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22312step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def raw22312step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22312 raw22312Labels = mixedMoment B node4067 node4067Labels := by
  calc
    mixedMoment B raw22312 raw22312Labels = mixedMoment B raw22312step0 raw22312step0Labels := by
      have hz : ∀ j, raw22312 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22312step0 = (fun i j => raw22312 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22312step0 raw22312; decide +kernel
      have hl : raw22312step0Labels = raw22312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22312 raw22312Labels permutation434 hz
    mixedMoment B raw22312step0 raw22312step0Labels = mixedMoment B raw22312step1 raw22312step1Labels := by
      have hz : ∀ j, raw22312step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22312step1 = (fun i j => raw22312step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22312step1 raw22312step0; decide +kernel
      have hl : raw22312step1Labels = raw22312step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22312step0 raw22312step0Labels permutation56 hz
    mixedMoment B raw22312step1 raw22312step1Labels = mixedMoment B raw22312step2 raw22312step2Labels := by
      have hz : ∀ i, raw22312step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22312step2 = (fun i j => raw22312step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22312step2 raw22312step1; decide +kernel
      have hl : raw22312step2Labels = (fun j => raw22312step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22312step1 raw22312step1Labels permutation6 hz
    _ = mixedMoment B node4067 node4067Labels := by rfl

def raw22313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22313Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22313step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22313step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw22313step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw22313step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def raw22313step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22313 raw22313Labels = mixedMoment B node4067 node4067Labels := by
  calc
    mixedMoment B raw22313 raw22313Labels = mixedMoment B raw22313step0 raw22313step0Labels := by
      have hz : ∀ j, raw22313 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22313step0 = (fun i j => raw22313 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22313step0 raw22313; decide +kernel
      have hl : raw22313step0Labels = raw22313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22313 raw22313Labels permutation346 hz
    mixedMoment B raw22313step0 raw22313step0Labels = mixedMoment B raw22313step1 raw22313step1Labels := by
      have hz : ∀ j, raw22313step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22313step1 = (fun i j => raw22313step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22313step1 raw22313step0; decide +kernel
      have hl : raw22313step1Labels = raw22313step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22313step0 raw22313step0Labels permutation56 hz
    mixedMoment B raw22313step1 raw22313step1Labels = mixedMoment B raw22313step2 raw22313step2Labels := by
      have hz : ∀ i, raw22313step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw22313step2 = (fun i j => raw22313step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw22313step2 raw22313step1; decide +kernel
      have hl : raw22313step2Labels = (fun j => raw22313step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw22313step1 raw22313step1Labels permutation6 hz
    _ = mixedMoment B node4067 node4067Labels := by rfl

def raw22314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22314Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22314step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22314step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22314step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22314 raw22314Labels = mixedMoment B node616 node616Labels := by
  calc
    mixedMoment B raw22314 raw22314Labels = mixedMoment B raw22314step0 raw22314step0Labels := by
      have hz : ∀ j, raw22314 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22314step0 = (fun i j => raw22314 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22314step0 raw22314; decide +kernel
      have hl : raw22314step0Labels = raw22314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22314 raw22314Labels permutation346 hz
    mixedMoment B raw22314step0 raw22314step0Labels = mixedMoment B raw22314step1 raw22314step1Labels := by
      have hz : ∀ j, raw22314step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22314step1 = (fun i j => raw22314step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22314step1 raw22314step0; decide +kernel
      have hl : raw22314step1Labels = raw22314step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22314step0 raw22314step0Labels permutation56 hz
    _ = mixedMoment B node616 node616Labels := by rfl

def raw22315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22315step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22315 raw22315Labels = mixedMoment B node935 node935Labels := by
  calc
    mixedMoment B raw22315 raw22315Labels = mixedMoment B raw22315step0 raw22315step0Labels := by
      have hz : ∀ j, raw22315 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22315step0 = (fun i j => raw22315 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22315step0 raw22315; decide +kernel
      have hl : raw22315step0Labels = raw22315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22315 raw22315Labels permutation346 hz
    _ = mixedMoment B node935 node935Labels := by rfl

def raw22316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22316step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22316 raw22316Labels = mixedMoment B node935 node935Labels := by
  calc
    mixedMoment B raw22316 raw22316Labels = mixedMoment B raw22316step0 raw22316step0Labels := by
      have hz : ∀ j, raw22316 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22316step0 = (fun i j => raw22316 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22316step0 raw22316; decide +kernel
      have hl : raw22316step0Labels = raw22316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22316 raw22316Labels permutation265 hz
    _ = mixedMoment B node935 node935Labels := by rfl

def raw22317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22317step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22317 raw22317Labels = mixedMoment B node1063 node1063Labels := by
  calc
    mixedMoment B raw22317 raw22317Labels = mixedMoment B raw22317step0 raw22317step0Labels := by
      have hz : ∀ j, raw22317 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22317step0 = (fun i j => raw22317 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22317step0 raw22317; decide +kernel
      have hl : raw22317step0Labels = raw22317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22317 raw22317Labels permutation346 hz
    mixedMoment B raw22317step0 raw22317step0Labels = mixedMoment B raw22317step1 raw22317step1Labels := by
      have hz : ∀ j, raw22317step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22317step1 = (fun i j => raw22317step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22317step1 raw22317step0; decide +kernel
      have hl : raw22317step1Labels = raw22317step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22317step0 raw22317step0Labels permutation56 hz
    _ = mixedMoment B node1063 node1063Labels := by rfl

def raw22318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw22318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw22318step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22318step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw22318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22318step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22318 raw22318Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw22318 raw22318Labels = mixedMoment B raw22318step0 raw22318step0Labels := by
      have hz : ∀ j, raw22318 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22318step0 = (fun i j => raw22318 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22318step0 raw22318; decide +kernel
      have hl : raw22318step0Labels = raw22318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22318 raw22318Labels permutation346 hz
    mixedMoment B raw22318step0 raw22318step0Labels = mixedMoment B raw22318step1 raw22318step1Labels := by
      have hz : ∀ j, raw22318step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22318step1 = (fun i j => raw22318step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22318step1 raw22318step0; decide +kernel
      have hl : raw22318step1Labels = raw22318step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22318step0 raw22318step0Labels permutation56 hz
    mixedMoment B raw22318step1 raw22318step1Labels = mixedMoment B raw22318step2 raw22318step2Labels := by
      have ha : raw22318step2 = (fun i j => raw22318step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22318step2 raw22318step1; decide +kernel
      have hl : raw22318step2Labels = raw22318step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22318step1 raw22318step1Labels permutation12 permutation2
    _ = mixedMoment B node1087 node1087Labels := by rfl

def raw22319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22319Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22319step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22319step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22319 raw22319Labels = mixedMoment B node1318 node1318Labels := by
  calc
    mixedMoment B raw22319 raw22319Labels = mixedMoment B raw22319step0 raw22319step0Labels := by
      have hz : ∀ j, raw22319 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22319step0 = (fun i j => raw22319 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22319step0 raw22319; decide +kernel
      have hl : raw22319step0Labels = raw22319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22319 raw22319Labels permutation346 hz
    mixedMoment B raw22319step0 raw22319step0Labels = mixedMoment B raw22319step1 raw22319step1Labels := by
      have ha : raw22319step1 = (fun i j => raw22319step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22319step1 raw22319step0; decide +kernel
      have hl : raw22319step1Labels = raw22319step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22319step0 raw22319step0Labels permutation39 permutation2
    _ = mixedMoment B node1318 node1318Labels := by rfl

def raw22320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw22320step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22320 raw22320Labels = mixedMoment B node1318 node1318Labels := by
  calc
    mixedMoment B raw22320 raw22320Labels = mixedMoment B raw22320step0 raw22320step0Labels := by
      have hz : ∀ j, raw22320 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22320step0 = (fun i j => raw22320 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22320step0 raw22320; decide +kernel
      have hl : raw22320step0Labels = raw22320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22320 raw22320Labels permutation265 hz
    mixedMoment B raw22320step0 raw22320step0Labels = mixedMoment B raw22320step1 raw22320step1Labels := by
      have ha : raw22320step1 = (fun i j => raw22320step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22320step1 raw22320step0; decide +kernel
      have hl : raw22320step1Labels = raw22320step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22320step0 raw22320step0Labels permutation39 permutation2
    _ = mixedMoment B node1318 node1318Labels := by rfl

def raw22321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw22321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw22321step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22321step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw22321step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22321step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw22321step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22321 raw22321Labels = mixedMoment B node1324 node1324Labels := by
  calc
    mixedMoment B raw22321 raw22321Labels = mixedMoment B raw22321step0 raw22321step0Labels := by
      have hz : ∀ j, raw22321 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22321step0 = (fun i j => raw22321 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22321step0 raw22321; decide +kernel
      have hl : raw22321step0Labels = raw22321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22321 raw22321Labels permutation346 hz
    mixedMoment B raw22321step0 raw22321step0Labels = mixedMoment B raw22321step1 raw22321step1Labels := by
      have hz : ∀ j, raw22321step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22321step1 = (fun i j => raw22321step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22321step1 raw22321step0; decide +kernel
      have hl : raw22321step1Labels = raw22321step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22321step0 raw22321step0Labels permutation56 hz
    mixedMoment B raw22321step1 raw22321step1Labels = mixedMoment B raw22321step2 raw22321step2Labels := by
      have ha : raw22321step2 = (fun i j => raw22321step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22321step2 raw22321step1; decide +kernel
      have hl : raw22321step2Labels = raw22321step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22321step1 raw22321step1Labels permutation9 permutation2
    _ = mixedMoment B node1324 node1324Labels := by rfl

def raw22322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw22322Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw22322step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, -1, 2], ![2, 0, -2], ![3, -2, -1]]
def raw22322step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22322 raw22322Labels = mixedMoment B node1325 node1325Labels := by
  calc
    mixedMoment B raw22322 raw22322Labels = mixedMoment B raw22322step0 raw22322step0Labels := by
      have hz : ∀ j, raw22322 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22322step0 = (fun i j => raw22322 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22322step0 raw22322; decide +kernel
      have hl : raw22322step0Labels = raw22322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22322 raw22322Labels permutation346 hz
    mixedMoment B raw22322step0 raw22322step0Labels = mixedMoment B raw22322step1 raw22322step1Labels := by
      have hz : ∀ j, raw22322step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22322step1 = (fun i j => raw22322step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22322step1 raw22322step0; decide +kernel
      have hl : raw22322step1Labels = raw22322step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22322step0 raw22322step0Labels permutation56 hz
    _ = mixedMoment B node1325 node1325Labels := by rfl

def raw22323 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22323step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22323step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw22323step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22323step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22323step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22323 raw22323Labels = mixedMoment B node1740 node1740Labels := by
  calc
    mixedMoment B raw22323 raw22323Labels = mixedMoment B raw22323step0 raw22323step0Labels := by
      have hz : ∀ j, raw22323 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22323step0 = (fun i j => raw22323 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22323step0 raw22323; decide +kernel
      have hl : raw22323step0Labels = raw22323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22323 raw22323Labels permutation346 hz
    mixedMoment B raw22323step0 raw22323step0Labels = mixedMoment B raw22323step1 raw22323step1Labels := by
      have hz : ∀ j, raw22323step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22323step1 = (fun i j => raw22323step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22323step1 raw22323step0; decide +kernel
      have hl : raw22323step1Labels = raw22323step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22323step0 raw22323step0Labels permutation56 hz
    mixedMoment B raw22323step1 raw22323step1Labels = mixedMoment B raw22323step2 raw22323step2Labels := by
      have ha : raw22323step2 = (fun i j => raw22323step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22323step2 raw22323step1; decide +kernel
      have hl : raw22323step2Labels = raw22323step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22323step1 raw22323step1Labels permutation11 permutation4
    mixedMoment B raw22323step2 raw22323step2Labels = mixedMoment B raw22323step3 raw22323step3Labels := by
      have ha : raw22323step3 = -raw22323step2 := by apply Matrix.ext; change ∀ i j, raw22323step3 i j = -(raw22323step2 i j); unfold raw22323step3 raw22323step2; decide +kernel
      have hl : raw22323step3Labels = raw22323step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1740 node1740Labels := by rfl

def raw22324 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22324Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22324step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22324step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22324step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22324 raw22324Labels = mixedMoment B node3243 node3243Labels := by
  calc
    mixedMoment B raw22324 raw22324Labels = mixedMoment B raw22324step0 raw22324step0Labels := by
      have hz : ∀ j, raw22324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22324step0 = (fun i j => raw22324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22324step0 raw22324; decide +kernel
      have hl : raw22324step0Labels = raw22324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22324 raw22324Labels permutation346 hz
    mixedMoment B raw22324step0 raw22324step0Labels = mixedMoment B raw22324step1 raw22324step1Labels := by
      have ha : raw22324step1 = (fun i j => raw22324step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22324step1 raw22324step0; decide +kernel
      have hl : raw22324step1Labels = raw22324step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22324step0 raw22324step0Labels permutation39 permutation2
    mixedMoment B raw22324step1 raw22324step1Labels = mixedMoment B raw22324step2 raw22324step2Labels := by
      have ha : raw22324step2 = -raw22324step1 := by apply Matrix.ext; change ∀ i j, raw22324step2 i j = -(raw22324step1 i j); unfold raw22324step2 raw22324step1; decide +kernel
      have hl : raw22324step2Labels = raw22324step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3243 node3243Labels := by rfl

def raw22325 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22325Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22325step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22325step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22325step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22325 raw22325Labels = mixedMoment B node3243 node3243Labels := by
  calc
    mixedMoment B raw22325 raw22325Labels = mixedMoment B raw22325step0 raw22325step0Labels := by
      have hz : ∀ j, raw22325 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22325step0 = (fun i j => raw22325 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22325step0 raw22325; decide +kernel
      have hl : raw22325step0Labels = raw22325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22325 raw22325Labels permutation265 hz
    mixedMoment B raw22325step0 raw22325step0Labels = mixedMoment B raw22325step1 raw22325step1Labels := by
      have ha : raw22325step1 = (fun i j => raw22325step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22325step1 raw22325step0; decide +kernel
      have hl : raw22325step1Labels = raw22325step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22325step0 raw22325step0Labels permutation39 permutation2
    mixedMoment B raw22325step1 raw22325step1Labels = mixedMoment B raw22325step2 raw22325step2Labels := by
      have ha : raw22325step2 = -raw22325step1 := by apply Matrix.ext; change ∀ i j, raw22325step2 i j = -(raw22325step1 i j); unfold raw22325step2 raw22325step1; decide +kernel
      have hl : raw22325step2Labels = raw22325step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3243 node3243Labels := by rfl

def raw22326 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22326Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22326step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22326step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22326step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22326step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22326step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22326step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22326 raw22326Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw22326 raw22326Labels = mixedMoment B raw22326step0 raw22326step0Labels := by
      have hz : ∀ j, raw22326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22326step0 = (fun i j => raw22326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22326step0 raw22326; decide +kernel
      have hl : raw22326step0Labels = raw22326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22326 raw22326Labels permutation346 hz
    mixedMoment B raw22326step0 raw22326step0Labels = mixedMoment B raw22326step1 raw22326step1Labels := by
      have hz : ∀ j, raw22326step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22326step1 = (fun i j => raw22326step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22326step1 raw22326step0; decide +kernel
      have hl : raw22326step1Labels = raw22326step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22326step0 raw22326step0Labels permutation56 hz
    mixedMoment B raw22326step1 raw22326step1Labels = mixedMoment B raw22326step2 raw22326step2Labels := by
      have ha : raw22326step2 = (fun i j => raw22326step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22326step2 raw22326step1; decide +kernel
      have hl : raw22326step2Labels = raw22326step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22326step1 raw22326step1Labels permutation9 permutation2
    mixedMoment B raw22326step2 raw22326step2Labels = mixedMoment B raw22326step3 raw22326step3Labels := by
      have ha : raw22326step3 = -raw22326step2 := by apply Matrix.ext; change ∀ i j, raw22326step3 i j = -(raw22326step2 i j); unfold raw22326step3 raw22326step2; decide +kernel
      have hl : raw22326step3Labels = raw22326step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3301 node3301Labels := by rfl

def raw22327 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw22327Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw22327step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22327step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw22327step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22327step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -2, 0], ![2, 2, -4]]
def raw22327step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22327 raw22327Labels = mixedMoment B node2409 node2409Labels := by
  calc
    mixedMoment B raw22327 raw22327Labels = mixedMoment B raw22327step0 raw22327step0Labels := by
      have hz : ∀ j, raw22327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22327step0 = (fun i j => raw22327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22327step0 raw22327; decide +kernel
      have hl : raw22327step0Labels = raw22327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22327 raw22327Labels permutation346 hz
    mixedMoment B raw22327step0 raw22327step0Labels = mixedMoment B raw22327step1 raw22327step1Labels := by
      have hz : ∀ j, raw22327step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22327step1 = (fun i j => raw22327step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22327step1 raw22327step0; decide +kernel
      have hl : raw22327step1Labels = raw22327step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22327step0 raw22327step0Labels permutation56 hz
    mixedMoment B raw22327step1 raw22327step1Labels = mixedMoment B raw22327step2 raw22327step2Labels := by
      have ha : raw22327step2 = (fun i j => raw22327step1 (permutation25 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22327step2 raw22327step1; decide +kernel
      have hl : raw22327step2Labels = raw22327step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22327step1 raw22327step1Labels permutation25 permutation2
    _ = mixedMoment B node2409 node2409Labels := by rfl

def raw22328 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22328Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22328step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22328step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22328step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22328step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22328 raw22328Labels = mixedMoment B node3248 node3248Labels := by
  calc
    mixedMoment B raw22328 raw22328Labels = mixedMoment B raw22328step0 raw22328step0Labels := by
      have hz : ∀ j, raw22328 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22328step0 = (fun i j => raw22328 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22328step0 raw22328; decide +kernel
      have hl : raw22328step0Labels = raw22328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22328 raw22328Labels permutation346 hz
    mixedMoment B raw22328step0 raw22328step0Labels = mixedMoment B raw22328step1 raw22328step1Labels := by
      have hz : ∀ j, raw22328step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22328step1 = (fun i j => raw22328step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22328step1 raw22328step0; decide +kernel
      have hl : raw22328step1Labels = raw22328step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22328step0 raw22328step0Labels permutation56 hz
    mixedMoment B raw22328step1 raw22328step1Labels = mixedMoment B raw22328step2 raw22328step2Labels := by
      have ha : raw22328step2 = -raw22328step1 := by apply Matrix.ext; change ∀ i j, raw22328step2 i j = -(raw22328step1 i j); unfold raw22328step2 raw22328step1; decide +kernel
      have hl : raw22328step2Labels = raw22328step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3248 node3248Labels := by rfl

def raw22329 : Matrix (Fin 6) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![0, 0], ![0, 0], ![-2, 2], ![-2, 2]]
def raw22329Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22329step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![0, 0], ![-2, 2], ![-2, 2]]
def raw22329step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22329step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![0, 0], ![-2, 2], ![-2, 2]]
def raw22329step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22329step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-2, 2], ![-2, 2]]
def raw22329step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22329step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw22329step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22329 raw22329Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw22329 raw22329Labels = mixedMoment B raw22329step0 raw22329step0Labels := by
      have hz : ∀ j, raw22329 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22329step0 = (fun i j => raw22329 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22329step0 raw22329; decide +kernel
      have hl : raw22329step0Labels = raw22329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22329 raw22329Labels permutation434 hz
    mixedMoment B raw22329step0 raw22329step0Labels = mixedMoment B raw22329step1 raw22329step1Labels := by
      have hz : ∀ j, raw22329step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22329step1 = (fun i j => raw22329step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22329step1 raw22329step0; decide +kernel
      have hl : raw22329step1Labels = raw22329step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22329step0 raw22329step0Labels permutation80 hz
    mixedMoment B raw22329step1 raw22329step1Labels = mixedMoment B raw22329step2 raw22329step2Labels := by
      have hz : ∀ j, raw22329step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw22329step2 = (fun i j => raw22329step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw22329step2 raw22329step1; decide +kernel
      have hl : raw22329step2Labels = raw22329step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22329step1 raw22329step1Labels permutation14 hz
    mixedMoment B raw22329step2 raw22329step2Labels = mixedMoment B raw22329step3 raw22329step3Labels := by
      have ha : raw22329step3 = -raw22329step2 := by apply Matrix.ext; change ∀ i j, raw22329step3 i j = -(raw22329step2 i j); unfold raw22329step3 raw22329step2; decide +kernel
      have hl : raw22329step3Labels = raw22329step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4071 node4071Labels := by rfl

def raw22330 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw22330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw22330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22330 raw22330Labels = mixedMoment B node1736 node1736Labels := by
  calc
    mixedMoment B raw22330 raw22330Labels = mixedMoment B raw22330step0 raw22330step0Labels := by
      have hz : ∀ j, raw22330 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22330step0 = (fun i j => raw22330 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22330step0 raw22330; decide +kernel
      have hl : raw22330step0Labels = raw22330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22330 raw22330Labels permutation346 hz
    mixedMoment B raw22330step0 raw22330step0Labels = mixedMoment B raw22330step1 raw22330step1Labels := by
      have ha : raw22330step1 = (fun i j => raw22330step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22330step1 raw22330step0; decide +kernel
      have hl : raw22330step1Labels = raw22330step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22330step0 raw22330step0Labels permutation44 permutation4
    mixedMoment B raw22330step1 raw22330step1Labels = mixedMoment B raw22330step2 raw22330step2Labels := by
      have ha : raw22330step2 = -raw22330step1 := by apply Matrix.ext; change ∀ i j, raw22330step2 i j = -(raw22330step1 i j); unfold raw22330step2 raw22330step1; decide +kernel
      have hl : raw22330step2Labels = raw22330step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1736 node1736Labels := by rfl

def raw22331 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw22331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw22331step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22331 raw22331Labels = mixedMoment B node1736 node1736Labels := by
  calc
    mixedMoment B raw22331 raw22331Labels = mixedMoment B raw22331step0 raw22331step0Labels := by
      have hz : ∀ j, raw22331 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22331step0 = (fun i j => raw22331 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22331step0 raw22331; decide +kernel
      have hl : raw22331step0Labels = raw22331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22331 raw22331Labels permutation265 hz
    mixedMoment B raw22331step0 raw22331step0Labels = mixedMoment B raw22331step1 raw22331step1Labels := by
      have ha : raw22331step1 = (fun i j => raw22331step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22331step1 raw22331step0; decide +kernel
      have hl : raw22331step1Labels = raw22331step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22331step0 raw22331step0Labels permutation44 permutation4
    mixedMoment B raw22331step1 raw22331step1Labels = mixedMoment B raw22331step2 raw22331step2Labels := by
      have ha : raw22331step2 = -raw22331step1 := by apply Matrix.ext; change ∀ i j, raw22331step2 i j = -(raw22331step1 i j); unfold raw22331step2 raw22331step1; decide +kernel
      have hl : raw22331step2Labels = raw22331step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1736 node1736Labels := by rfl

def raw22332 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22332Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22332step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22332step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22332step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22332step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22332step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22332 raw22332Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw22332 raw22332Labels = mixedMoment B raw22332step0 raw22332step0Labels := by
      have hz : ∀ j, raw22332 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22332step0 = (fun i j => raw22332 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22332step0 raw22332; decide +kernel
      have hl : raw22332step0Labels = raw22332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22332 raw22332Labels permutation346 hz
    mixedMoment B raw22332step0 raw22332step0Labels = mixedMoment B raw22332step1 raw22332step1Labels := by
      have hz : ∀ j, raw22332step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22332step1 = (fun i j => raw22332step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22332step1 raw22332step0; decide +kernel
      have hl : raw22332step1Labels = raw22332step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22332step0 raw22332step0Labels permutation56 hz
    mixedMoment B raw22332step1 raw22332step1Labels = mixedMoment B raw22332step2 raw22332step2Labels := by
      have ha : raw22332step2 = (fun i j => raw22332step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22332step2 raw22332step1; decide +kernel
      have hl : raw22332step2Labels = raw22332step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22332step1 raw22332step1Labels permutation8 permutation4
    mixedMoment B raw22332step2 raw22332step2Labels = mixedMoment B raw22332step3 raw22332step3Labels := by
      have ha : raw22332step3 = -raw22332step2 := by apply Matrix.ext; change ∀ i j, raw22332step3 i j = -(raw22332step2 i j); unfold raw22332step3 raw22332step2; decide +kernel
      have hl : raw22332step3Labels = raw22332step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1751 node1751Labels := by rfl

def raw22333 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22333Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22333step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22333step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22333step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22333step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22333step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22333step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22333 raw22333Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw22333 raw22333Labels = mixedMoment B raw22333step0 raw22333step0Labels := by
      have hz : ∀ j, raw22333 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22333step0 = (fun i j => raw22333 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22333step0 raw22333; decide +kernel
      have hl : raw22333step0Labels = raw22333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22333 raw22333Labels permutation346 hz
    mixedMoment B raw22333step0 raw22333step0Labels = mixedMoment B raw22333step1 raw22333step1Labels := by
      have hz : ∀ j, raw22333step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22333step1 = (fun i j => raw22333step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22333step1 raw22333step0; decide +kernel
      have hl : raw22333step1Labels = raw22333step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22333step0 raw22333step0Labels permutation56 hz
    mixedMoment B raw22333step1 raw22333step1Labels = mixedMoment B raw22333step2 raw22333step2Labels := by
      have ha : raw22333step2 = (fun i j => raw22333step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22333step2 raw22333step1; decide +kernel
      have hl : raw22333step2Labels = raw22333step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22333step1 raw22333step1Labels permutation10 permutation4
    mixedMoment B raw22333step2 raw22333step2Labels = mixedMoment B raw22333step3 raw22333step3Labels := by
      have ha : raw22333step3 = -raw22333step2 := by apply Matrix.ext; change ∀ i j, raw22333step3 i j = -(raw22333step2 i j); unfold raw22333step3 raw22333step2; decide +kernel
      have hl : raw22333step3Labels = raw22333step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1738 node1738Labels := by rfl

def raw22334 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22334Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22334step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22334step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw22334step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22334step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22334step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22334 raw22334Labels = mixedMoment B node858 node858Labels := by
  calc
    mixedMoment B raw22334 raw22334Labels = mixedMoment B raw22334step0 raw22334step0Labels := by
      have hz : ∀ j, raw22334 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22334step0 = (fun i j => raw22334 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22334step0 raw22334; decide +kernel
      have hl : raw22334step0Labels = raw22334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22334 raw22334Labels permutation346 hz
    mixedMoment B raw22334step0 raw22334step0Labels = mixedMoment B raw22334step1 raw22334step1Labels := by
      have hz : ∀ j, raw22334step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22334step1 = (fun i j => raw22334step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22334step1 raw22334step0; decide +kernel
      have hl : raw22334step1Labels = raw22334step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22334step0 raw22334step0Labels permutation56 hz
    mixedMoment B raw22334step1 raw22334step1Labels = mixedMoment B raw22334step2 raw22334step2Labels := by
      have ha : raw22334step2 = (fun i j => raw22334step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22334step2 raw22334step1; decide +kernel
      have hl : raw22334step2Labels = raw22334step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22334step1 raw22334step1Labels permutation11 permutation4
    mixedMoment B raw22334step2 raw22334step2Labels = mixedMoment B raw22334step3 raw22334step3Labels := by
      have ha : raw22334step3 = -raw22334step2 := by apply Matrix.ext; change ∀ i j, raw22334step3 i j = -(raw22334step2 i j); unfold raw22334step3 raw22334step2; decide +kernel
      have hl : raw22334step3Labels = raw22334step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node858 node858Labels := by rfl

def raw22335 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw22335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22335step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22335step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22335 raw22335Labels = mixedMoment B node1626 node1626Labels := by
  calc
    mixedMoment B raw22335 raw22335Labels = mixedMoment B raw22335step0 raw22335step0Labels := by
      have hz : ∀ j, raw22335 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22335step0 = (fun i j => raw22335 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22335step0 raw22335; decide +kernel
      have hl : raw22335step0Labels = raw22335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22335 raw22335Labels permutation346 hz
    mixedMoment B raw22335step0 raw22335step0Labels = mixedMoment B raw22335step1 raw22335step1Labels := by
      have ha : raw22335step1 = (fun i j => raw22335step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22335step1 raw22335step0; decide +kernel
      have hl : raw22335step1Labels = raw22335step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22335step0 raw22335step0Labels permutation35 permutation4
    mixedMoment B raw22335step1 raw22335step1Labels = mixedMoment B raw22335step2 raw22335step2Labels := by
      have ha : raw22335step2 = -raw22335step1 := by apply Matrix.ext; change ∀ i j, raw22335step2 i j = -(raw22335step1 i j); unfold raw22335step2 raw22335step1; decide +kernel
      have hl : raw22335step2Labels = raw22335step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1626 node1626Labels := by rfl

def raw22336 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw22336step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22336step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22336step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22336 raw22336Labels = mixedMoment B node1626 node1626Labels := by
  calc
    mixedMoment B raw22336 raw22336Labels = mixedMoment B raw22336step0 raw22336step0Labels := by
      have hz : ∀ j, raw22336 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22336step0 = (fun i j => raw22336 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22336step0 raw22336; decide +kernel
      have hl : raw22336step0Labels = raw22336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22336 raw22336Labels permutation265 hz
    mixedMoment B raw22336step0 raw22336step0Labels = mixedMoment B raw22336step1 raw22336step1Labels := by
      have ha : raw22336step1 = (fun i j => raw22336step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22336step1 raw22336step0; decide +kernel
      have hl : raw22336step1Labels = raw22336step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22336step0 raw22336step0Labels permutation35 permutation4
    mixedMoment B raw22336step1 raw22336step1Labels = mixedMoment B raw22336step2 raw22336step2Labels := by
      have ha : raw22336step2 = -raw22336step1 := by apply Matrix.ext; change ∀ i j, raw22336step2 i j = -(raw22336step1 i j); unfold raw22336step2 raw22336step1; decide +kernel
      have hl : raw22336step2Labels = raw22336step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1626 node1626Labels := by rfl

def raw22337 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22337step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22337step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw22337step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22337step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw22337step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22337 raw22337Labels = mixedMoment B node1740 node1740Labels := by
  calc
    mixedMoment B raw22337 raw22337Labels = mixedMoment B raw22337step0 raw22337step0Labels := by
      have hz : ∀ j, raw22337 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22337step0 = (fun i j => raw22337 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22337step0 raw22337; decide +kernel
      have hl : raw22337step0Labels = raw22337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22337 raw22337Labels permutation346 hz
    mixedMoment B raw22337step0 raw22337step0Labels = mixedMoment B raw22337step1 raw22337step1Labels := by
      have hz : ∀ j, raw22337step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22337step1 = (fun i j => raw22337step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22337step1 raw22337step0; decide +kernel
      have hl : raw22337step1Labels = raw22337step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22337step0 raw22337step0Labels permutation56 hz
    mixedMoment B raw22337step1 raw22337step1Labels = mixedMoment B raw22337step2 raw22337step2Labels := by
      have ha : raw22337step2 = (fun i j => raw22337step1 (permutation13 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22337step2 raw22337step1; decide +kernel
      have hl : raw22337step2Labels = raw22337step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22337step1 raw22337step1Labels permutation13 permutation4
    mixedMoment B raw22337step2 raw22337step2Labels = mixedMoment B raw22337step3 raw22337step3Labels := by
      have ha : raw22337step3 = -raw22337step2 := by apply Matrix.ext; change ∀ i j, raw22337step3 i j = -(raw22337step2 i j); unfold raw22337step3 raw22337step2; decide +kernel
      have hl : raw22337step3Labels = raw22337step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1740 node1740Labels := by rfl

def raw22338 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22338step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22338step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw22338step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22338step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22338step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22338 raw22338Labels = mixedMoment B node830 node830Labels := by
  calc
    mixedMoment B raw22338 raw22338Labels = mixedMoment B raw22338step0 raw22338step0Labels := by
      have hz : ∀ j, raw22338 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22338step0 = (fun i j => raw22338 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22338step0 raw22338; decide +kernel
      have hl : raw22338step0Labels = raw22338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22338 raw22338Labels permutation346 hz
    mixedMoment B raw22338step0 raw22338step0Labels = mixedMoment B raw22338step1 raw22338step1Labels := by
      have hz : ∀ j, raw22338step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22338step1 = (fun i j => raw22338step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22338step1 raw22338step0; decide +kernel
      have hl : raw22338step1Labels = raw22338step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22338step0 raw22338step0Labels permutation56 hz
    mixedMoment B raw22338step1 raw22338step1Labels = mixedMoment B raw22338step2 raw22338step2Labels := by
      have ha : raw22338step2 = (fun i j => raw22338step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22338step2 raw22338step1; decide +kernel
      have hl : raw22338step2Labels = raw22338step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22338step1 raw22338step1Labels permutation10 permutation4
    mixedMoment B raw22338step2 raw22338step2Labels = mixedMoment B raw22338step3 raw22338step3Labels := by
      have ha : raw22338step3 = -raw22338step2 := by apply Matrix.ext; change ∀ i j, raw22338step3 i j = -(raw22338step2 i j); unfold raw22338step3 raw22338step2; decide +kernel
      have hl : raw22338step3Labels = raw22338step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node830 node830Labels := by rfl

def raw22339 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw22339step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22339step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22339step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22339 raw22339Labels = mixedMoment B node1611 node1611Labels := by
  calc
    mixedMoment B raw22339 raw22339Labels = mixedMoment B raw22339step0 raw22339step0Labels := by
      have hz : ∀ j, raw22339 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22339step0 = (fun i j => raw22339 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22339step0 raw22339; decide +kernel
      have hl : raw22339step0Labels = raw22339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22339 raw22339Labels permutation346 hz
    mixedMoment B raw22339step0 raw22339step0Labels = mixedMoment B raw22339step1 raw22339step1Labels := by
      have ha : raw22339step1 = (fun i j => raw22339step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22339step1 raw22339step0; decide +kernel
      have hl : raw22339step1Labels = raw22339step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22339step0 raw22339step0Labels permutation34 permutation4
    mixedMoment B raw22339step1 raw22339step1Labels = mixedMoment B raw22339step2 raw22339step2Labels := by
      have ha : raw22339step2 = -raw22339step1 := by apply Matrix.ext; change ∀ i j, raw22339step2 i j = -(raw22339step1 i j); unfold raw22339step2 raw22339step1; decide +kernel
      have hl : raw22339step2Labels = raw22339step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1611 node1611Labels := by rfl

def raw22340 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22340Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![2, -2, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw22340step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22340step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22340step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22340 raw22340Labels = mixedMoment B node1611 node1611Labels := by
  calc
    mixedMoment B raw22340 raw22340Labels = mixedMoment B raw22340step0 raw22340step0Labels := by
      have hz : ∀ j, raw22340 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22340step0 = (fun i j => raw22340 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22340step0 raw22340; decide +kernel
      have hl : raw22340step0Labels = raw22340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22340 raw22340Labels permutation265 hz
    mixedMoment B raw22340step0 raw22340step0Labels = mixedMoment B raw22340step1 raw22340step1Labels := by
      have ha : raw22340step1 = (fun i j => raw22340step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22340step1 raw22340step0; decide +kernel
      have hl : raw22340step1Labels = raw22340step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22340step0 raw22340step0Labels permutation34 permutation4
    mixedMoment B raw22340step1 raw22340step1Labels = mixedMoment B raw22340step2 raw22340step2Labels := by
      have ha : raw22340step2 = -raw22340step1 := by apply Matrix.ext; change ∀ i j, raw22340step2 i j = -(raw22340step1 i j); unfold raw22340step2 raw22340step1; decide +kernel
      have hl : raw22340step2Labels = raw22340step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1611 node1611Labels := by rfl

def raw22341 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22341step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22341step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw22341step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22341step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -2, 0], ![2, 0, -2]]
def raw22341step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22341 raw22341Labels = mixedMoment B node1660 node1660Labels := by
  calc
    mixedMoment B raw22341 raw22341Labels = mixedMoment B raw22341step0 raw22341step0Labels := by
      have hz : ∀ j, raw22341 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22341step0 = (fun i j => raw22341 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22341step0 raw22341; decide +kernel
      have hl : raw22341step0Labels = raw22341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22341 raw22341Labels permutation346 hz
    mixedMoment B raw22341step0 raw22341step0Labels = mixedMoment B raw22341step1 raw22341step1Labels := by
      have hz : ∀ j, raw22341step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22341step1 = (fun i j => raw22341step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22341step1 raw22341step0; decide +kernel
      have hl : raw22341step1Labels = raw22341step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22341step0 raw22341step0Labels permutation56 hz
    mixedMoment B raw22341step1 raw22341step1Labels = mixedMoment B raw22341step2 raw22341step2Labels := by
      have ha : raw22341step2 = (fun i j => raw22341step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22341step2 raw22341step1; decide +kernel
      have hl : raw22341step2Labels = raw22341step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22341step1 raw22341step1Labels permutation10 permutation4
    mixedMoment B raw22341step2 raw22341step2Labels = mixedMoment B raw22341step3 raw22341step3Labels := by
      have ha : raw22341step3 = -raw22341step2 := by apply Matrix.ext; change ∀ i j, raw22341step3 i j = -(raw22341step2 i j); unfold raw22341step3 raw22341step2; decide +kernel
      have hl : raw22341step3Labels = raw22341step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1660 node1660Labels := by rfl

def raw22342 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22342Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22342step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw22342step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22342step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw22342step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22342 raw22342Labels = mixedMoment B node1732 node1732Labels := by
  calc
    mixedMoment B raw22342 raw22342Labels = mixedMoment B raw22342step0 raw22342step0Labels := by
      have hz : ∀ j, raw22342 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22342step0 = (fun i j => raw22342 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22342step0 raw22342; decide +kernel
      have hl : raw22342step0Labels = raw22342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22342 raw22342Labels permutation346 hz
    mixedMoment B raw22342step0 raw22342step0Labels = mixedMoment B raw22342step1 raw22342step1Labels := by
      have ha : raw22342step1 = (fun i j => raw22342step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22342step1 raw22342step0; decide +kernel
      have hl : raw22342step1Labels = raw22342step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22342step0 raw22342step0Labels permutation48 permutation4
    mixedMoment B raw22342step1 raw22342step1Labels = mixedMoment B raw22342step2 raw22342step2Labels := by
      have ha : raw22342step2 = -raw22342step1 := by apply Matrix.ext; change ∀ i j, raw22342step2 i j = -(raw22342step1 i j); unfold raw22342step2 raw22342step1; decide +kernel
      have hl : raw22342step2Labels = raw22342step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1732 node1732Labels := by rfl

def raw22343 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22343Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22343step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw22343step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22343step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw22343step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22343 raw22343Labels = mixedMoment B node1732 node1732Labels := by
  calc
    mixedMoment B raw22343 raw22343Labels = mixedMoment B raw22343step0 raw22343step0Labels := by
      have hz : ∀ j, raw22343 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22343step0 = (fun i j => raw22343 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22343step0 raw22343; decide +kernel
      have hl : raw22343step0Labels = raw22343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22343 raw22343Labels permutation265 hz
    mixedMoment B raw22343step0 raw22343step0Labels = mixedMoment B raw22343step1 raw22343step1Labels := by
      have ha : raw22343step1 = (fun i j => raw22343step0 (permutation48 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22343step1 raw22343step0; decide +kernel
      have hl : raw22343step1Labels = raw22343step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22343step0 raw22343step0Labels permutation48 permutation4
    mixedMoment B raw22343step1 raw22343step1Labels = mixedMoment B raw22343step2 raw22343step2Labels := by
      have ha : raw22343step2 = -raw22343step1 := by apply Matrix.ext; change ∀ i j, raw22343step2 i j = -(raw22343step1 i j); unfold raw22343step2 raw22343step1; decide +kernel
      have hl : raw22343step2Labels = raw22343step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1732 node1732Labels := by rfl

def raw22344 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22344Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![3, -3, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22344step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22344step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![3, -3, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22344step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22344step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![0, -2, 2], ![-3, 3, 0]]
def raw22344step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22344step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 2, -2], ![3, -3, 0]]
def raw22344step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22344 raw22344Labels = mixedMoment B node1733 node1733Labels := by
  calc
    mixedMoment B raw22344 raw22344Labels = mixedMoment B raw22344step0 raw22344step0Labels := by
      have hz : ∀ j, raw22344 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22344step0 = (fun i j => raw22344 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22344step0 raw22344; decide +kernel
      have hl : raw22344step0Labels = raw22344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22344 raw22344Labels permutation346 hz
    mixedMoment B raw22344step0 raw22344step0Labels = mixedMoment B raw22344step1 raw22344step1Labels := by
      have hz : ∀ j, raw22344step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22344step1 = (fun i j => raw22344step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22344step1 raw22344step0; decide +kernel
      have hl : raw22344step1Labels = raw22344step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22344step0 raw22344step0Labels permutation56 hz
    mixedMoment B raw22344step1 raw22344step1Labels = mixedMoment B raw22344step2 raw22344step2Labels := by
      have ha : raw22344step2 = (fun i j => raw22344step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22344step2 raw22344step1; decide +kernel
      have hl : raw22344step2Labels = raw22344step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22344step1 raw22344step1Labels permutation11 permutation4
    mixedMoment B raw22344step2 raw22344step2Labels = mixedMoment B raw22344step3 raw22344step3Labels := by
      have ha : raw22344step3 = -raw22344step2 := by apply Matrix.ext; change ∀ i j, raw22344step3 i j = -(raw22344step2 i j); unfold raw22344step3 raw22344step2; decide +kernel
      have hl : raw22344step3Labels = raw22344step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1733 node1733Labels := by rfl

def raw22345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2], ![2, 0, -2]]
def raw22345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2], ![2, 0, -2]]
def raw22345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22345step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -3, 3], ![2, 0, -2], ![2, 0, -2]]
def raw22345step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22345 raw22345Labels = mixedMoment B node1353 node1353Labels := by
  calc
    mixedMoment B raw22345 raw22345Labels = mixedMoment B raw22345step0 raw22345step0Labels := by
      have hz : ∀ j, raw22345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22345step0 = (fun i j => raw22345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22345step0 raw22345; decide +kernel
      have hl : raw22345step0Labels = raw22345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22345 raw22345Labels permutation346 hz
    mixedMoment B raw22345step0 raw22345step0Labels = mixedMoment B raw22345step1 raw22345step1Labels := by
      have hz : ∀ j, raw22345step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22345step1 = (fun i j => raw22345step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22345step1 raw22345step0; decide +kernel
      have hl : raw22345step1Labels = raw22345step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22345step0 raw22345step0Labels permutation56 hz
    _ = mixedMoment B node1353 node1353Labels := by rfl

def raw22346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2], ![2, 0, -2]]
def raw22346Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -3, 3], ![2, 0, -2], ![2, 0, -2]]
def raw22346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw22346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22346 raw22346Labels = mixedMoment B node2271 node2271Labels := by
  calc
    mixedMoment B raw22346 raw22346Labels = mixedMoment B raw22346step0 raw22346step0Labels := by
      have hz : ∀ j, raw22346 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22346step0 = (fun i j => raw22346 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22346step0 raw22346; decide +kernel
      have hl : raw22346step0Labels = raw22346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22346 raw22346Labels permutation346 hz
    mixedMoment B raw22346step0 raw22346step0Labels = mixedMoment B raw22346step1 raw22346step1Labels := by
      have ha : raw22346step1 = (fun i j => raw22346step0 (permutation97 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22346step1 raw22346step0; decide +kernel
      have hl : raw22346step1Labels = raw22346step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22346step0 raw22346step0Labels permutation97 permutation4
    _ = mixedMoment B node2271 node2271Labels := by rfl

def raw22347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3], ![2, 0, -2], ![2, 0, -2]]
def raw22347Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -3, 3], ![2, 0, -2], ![2, 0, -2]]
def raw22347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw22347step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22347 raw22347Labels = mixedMoment B node2271 node2271Labels := by
  calc
    mixedMoment B raw22347 raw22347Labels = mixedMoment B raw22347step0 raw22347step0Labels := by
      have hz : ∀ j, raw22347 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22347step0 = (fun i j => raw22347 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22347step0 raw22347; decide +kernel
      have hl : raw22347step0Labels = raw22347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22347 raw22347Labels permutation265 hz
    mixedMoment B raw22347step0 raw22347step0Labels = mixedMoment B raw22347step1 raw22347step1Labels := by
      have ha : raw22347step1 = (fun i j => raw22347step0 (permutation97 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22347step1 raw22347step0; decide +kernel
      have hl : raw22347step1Labels = raw22347step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22347step0 raw22347step0Labels permutation97 permutation4
    _ = mixedMoment B node2271 node2271Labels := by rfl

def raw22348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3], ![2, 0, -2], ![2, 0, -2]]
def raw22348Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, -2, 3], ![2, 0, -2], ![2, 0, -2]]
def raw22348step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22348step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, 0, -2], ![2, 0, -2]]
def raw22348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22348 raw22348Labels = mixedMoment B node2843 node2843Labels := by
  calc
    mixedMoment B raw22348 raw22348Labels = mixedMoment B raw22348step0 raw22348step0Labels := by
      have hz : ∀ j, raw22348 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22348step0 = (fun i j => raw22348 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22348step0 raw22348; decide +kernel
      have hl : raw22348step0Labels = raw22348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22348 raw22348Labels permutation346 hz
    mixedMoment B raw22348step0 raw22348step0Labels = mixedMoment B raw22348step1 raw22348step1Labels := by
      have hz : ∀ j, raw22348step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22348step1 = (fun i j => raw22348step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22348step1 raw22348step0; decide +kernel
      have hl : raw22348step1Labels = raw22348step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22348step0 raw22348step0Labels permutation56 hz
    _ = mixedMoment B node2843 node2843Labels := by rfl

def raw22349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![1, 1, -2], ![2, 0, -2]]
def raw22349Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -3, 3], ![1, 1, -2], ![2, 0, -2]]
def raw22349step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22349step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -3, 3], ![1, 1, -2], ![2, 0, -2]]
def raw22349step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22349step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw22349step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22349 raw22349Labels = mixedMoment B node2280 node2280Labels := by
  calc
    mixedMoment B raw22349 raw22349Labels = mixedMoment B raw22349step0 raw22349step0Labels := by
      have hz : ∀ j, raw22349 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22349step0 = (fun i j => raw22349 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22349step0 raw22349; decide +kernel
      have hl : raw22349step0Labels = raw22349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22349 raw22349Labels permutation346 hz
    mixedMoment B raw22349step0 raw22349step0Labels = mixedMoment B raw22349step1 raw22349step1Labels := by
      have hz : ∀ j, raw22349step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22349step1 = (fun i j => raw22349step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22349step1 raw22349step0; decide +kernel
      have hl : raw22349step1Labels = raw22349step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22349step0 raw22349step0Labels permutation56 hz
    mixedMoment B raw22349step1 raw22349step1Labels = mixedMoment B raw22349step2 raw22349step2Labels := by
      have ha : raw22349step2 = (fun i j => raw22349step1 (permutation19 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22349step2 raw22349step1; decide +kernel
      have hl : raw22349step2Labels = raw22349step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22349step1 raw22349step1Labels permutation19 permutation4
    _ = mixedMoment B node2280 node2280Labels := by rfl

def raw22350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2], ![1, 1, -2]]
def raw22350Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -3, 3], ![2, 0, -2], ![1, 1, -2]]
def raw22350step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22350step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -3, 3], ![2, 0, -2], ![1, 1, -2]]
def raw22350step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22350step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw22350step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22350 raw22350Labels = mixedMoment B node2280 node2280Labels := by
  calc
    mixedMoment B raw22350 raw22350Labels = mixedMoment B raw22350step0 raw22350step0Labels := by
      have hz : ∀ j, raw22350 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22350step0 = (fun i j => raw22350 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22350step0 raw22350; decide +kernel
      have hl : raw22350step0Labels = raw22350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22350 raw22350Labels permutation346 hz
    mixedMoment B raw22350step0 raw22350step0Labels = mixedMoment B raw22350step1 raw22350step1Labels := by
      have hz : ∀ j, raw22350step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22350step1 = (fun i j => raw22350step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22350step1 raw22350step0; decide +kernel
      have hl : raw22350step1Labels = raw22350step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22350step0 raw22350step0Labels permutation56 hz
    mixedMoment B raw22350step1 raw22350step1Labels = mixedMoment B raw22350step2 raw22350step2Labels := by
      have ha : raw22350step2 = (fun i j => raw22350step1 (permutation17 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22350step2 raw22350step1; decide +kernel
      have hl : raw22350step2Labels = raw22350step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22350step1 raw22350step1Labels permutation17 permutation4
    _ = mixedMoment B node2280 node2280Labels := by rfl

def raw22351 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![0, 0], ![-3, 3], ![2, -2], ![2, -2]]
def raw22351Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22351step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-3, 3], ![2, -2], ![2, -2]]
def raw22351step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22351step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![2, -2], ![2, -2]]
def raw22351step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22351step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw22351step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22351 raw22351Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw22351 raw22351Labels = mixedMoment B raw22351step0 raw22351step0Labels := by
      have hz : ∀ j, raw22351 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22351step0 = (fun i j => raw22351 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22351step0 raw22351; decide +kernel
      have hl : raw22351step0Labels = raw22351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22351 raw22351Labels permutation346 hz
    mixedMoment B raw22351step0 raw22351step0Labels = mixedMoment B raw22351step1 raw22351step1Labels := by
      have hz : ∀ j, raw22351step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22351step1 = (fun i j => raw22351step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22351step1 raw22351step0; decide +kernel
      have hl : raw22351step1Labels = raw22351step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22351step0 raw22351step0Labels permutation56 hz
    mixedMoment B raw22351step1 raw22351step1Labels = mixedMoment B raw22351step2 raw22351step2Labels := by
      have ha : raw22351step2 = (fun i j => raw22351step1 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22351step2 raw22351step1; decide +kernel
      have hl : raw22351step2Labels = raw22351step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22351step1 raw22351step1Labels permutation14 permutation0
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw22352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22352Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22352step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22352step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22352 raw22352Labels = mixedMoment B node586 node586Labels := by
  calc
    mixedMoment B raw22352 raw22352Labels = mixedMoment B raw22352step0 raw22352step0Labels := by
      have hz : ∀ j, raw22352 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22352step0 = (fun i j => raw22352 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22352step0 raw22352; decide +kernel
      have hl : raw22352step0Labels = raw22352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22352 raw22352Labels permutation265 hz
    mixedMoment B raw22352step0 raw22352step0Labels = mixedMoment B raw22352step1 raw22352step1Labels := by
      have ha : raw22352step1 = (fun i j => raw22352step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22352step1 raw22352step0; decide +kernel
      have hl : raw22352step1Labels = raw22352step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22352step0 raw22352step0Labels permutation38 permutation2
    _ = mixedMoment B node586 node586Labels := by rfl

def raw22353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22353Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22353step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22353 raw22353Labels = mixedMoment B node910 node910Labels := by
  calc
    mixedMoment B raw22353 raw22353Labels = mixedMoment B raw22353step0 raw22353step0Labels := by
      have ha : raw22353step0 = (fun i j => raw22353 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22353step0 raw22353; decide +kernel
      have hl : raw22353step0Labels = raw22353Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22353 raw22353Labels permutation158 permutation2
    _ = mixedMoment B node910 node910Labels := by rfl

def raw22354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22354Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22354step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22354 raw22354Labels = mixedMoment B node1026 node1026Labels := by
  calc
    mixedMoment B raw22354 raw22354Labels = mixedMoment B raw22354step0 raw22354step0Labels := by
      have hz : ∀ j, raw22354 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22354step0 = (fun i j => raw22354 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22354step0 raw22354; decide +kernel
      have hl : raw22354step0Labels = raw22354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22354 raw22354Labels permutation265 hz
    _ = mixedMoment B node1026 node1026Labels := by rfl

def raw22355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22355Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22355step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22355step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22355 raw22355Labels = mixedMoment B node950 node950Labels := by
  calc
    mixedMoment B raw22355 raw22355Labels = mixedMoment B raw22355step0 raw22355step0Labels := by
      have hz : ∀ j, raw22355 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22355step0 = (fun i j => raw22355 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22355step0 raw22355; decide +kernel
      have hl : raw22355step0Labels = raw22355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22355 raw22355Labels permutation265 hz
    mixedMoment B raw22355step0 raw22355step0Labels = mixedMoment B raw22355step1 raw22355step1Labels := by
      have ha : raw22355step1 = (fun i j => raw22355step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22355step1 raw22355step0; decide +kernel
      have hl : raw22355step1Labels = raw22355step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22355step0 raw22355step0Labels permutation38 permutation2
    _ = mixedMoment B node950 node950Labels := by rfl

def raw22356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw22356step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22356 raw22356Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw22356 raw22356Labels = mixedMoment B raw22356step0 raw22356step0Labels := by
      have hz : ∀ j, raw22356 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22356step0 = (fun i j => raw22356 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22356step0 raw22356; decide +kernel
      have hl : raw22356step0Labels = raw22356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22356 raw22356Labels permutation265 hz
    mixedMoment B raw22356step0 raw22356step0Labels = mixedMoment B raw22356step1 raw22356step1Labels := by
      have ha : raw22356step1 = (fun i j => raw22356step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22356step1 raw22356step0; decide +kernel
      have hl : raw22356step1Labels = raw22356step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22356step0 raw22356step0Labels permutation39 permutation2
    _ = mixedMoment B node1044 node1044Labels := by rfl

def raw22357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22357Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw22357step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22357 raw22357Labels = mixedMoment B node1328 node1328Labels := by
  calc
    mixedMoment B raw22357 raw22357Labels = mixedMoment B raw22357step0 raw22357step0Labels := by
      have ha : raw22357step0 = (fun i j => raw22357 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22357step0 raw22357; decide +kernel
      have hl : raw22357step0Labels = raw22357Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22357 raw22357Labels permutation183 permutation2
    _ = mixedMoment B node1328 node1328Labels := by rfl

def raw22358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22358Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, -1, -1]]
def raw22358step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw22358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22358 raw22358Labels = mixedMoment B node1338 node1338Labels := by
  calc
    mixedMoment B raw22358 raw22358Labels = mixedMoment B raw22358step0 raw22358step0Labels := by
      have hz : ∀ j, raw22358 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22358step0 = (fun i j => raw22358 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22358step0 raw22358; decide +kernel
      have hl : raw22358step0Labels = raw22358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22358 raw22358Labels permutation265 hz
    mixedMoment B raw22358step0 raw22358step0Labels = mixedMoment B raw22358step1 raw22358step1Labels := by
      have ha : raw22358step1 = (fun i j => raw22358step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22358step1 raw22358step0; decide +kernel
      have hl : raw22358step1Labels = raw22358step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22358step0 raw22358step0Labels permutation33 permutation2
    _ = mixedMoment B node1338 node1338Labels := by rfl

def raw22359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22359Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw22359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22359step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw22359step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22359 raw22359Labels = mixedMoment B node1333 node1333Labels := by
  calc
    mixedMoment B raw22359 raw22359Labels = mixedMoment B raw22359step0 raw22359step0Labels := by
      have hz : ∀ j, raw22359 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22359step0 = (fun i j => raw22359 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22359step0 raw22359; decide +kernel
      have hl : raw22359step0Labels = raw22359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22359 raw22359Labels permutation265 hz
    mixedMoment B raw22359step0 raw22359step0Labels = mixedMoment B raw22359step1 raw22359step1Labels := by
      have ha : raw22359step1 = (fun i j => raw22359step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22359step1 raw22359step0; decide +kernel
      have hl : raw22359step1Labels = raw22359step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22359step0 raw22359step0Labels permutation33 permutation2
    _ = mixedMoment B node1333 node1333Labels := by rfl

def raw22360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22360Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw22360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22360 raw22360Labels = mixedMoment B node1334 node1334Labels := by
  calc
    mixedMoment B raw22360 raw22360Labels = mixedMoment B raw22360step0 raw22360step0Labels := by
      have hz : ∀ j, raw22360 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22360step0 = (fun i j => raw22360 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22360step0 raw22360; decide +kernel
      have hl : raw22360step0Labels = raw22360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22360 raw22360Labels permutation265 hz
    _ = mixedMoment B node1334 node1334Labels := by rfl

def raw22361 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22361Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22361step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22361step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22361 raw22361Labels = mixedMoment B node3280 node3280Labels := by
  calc
    mixedMoment B raw22361 raw22361Labels = mixedMoment B raw22361step0 raw22361step0Labels := by
      have ha : raw22361step0 = (fun i j => raw22361 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22361step0 raw22361; decide +kernel
      have hl : raw22361step0Labels = raw22361Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22361 raw22361Labels permutation183 permutation2
    mixedMoment B raw22361step0 raw22361step0Labels = mixedMoment B raw22361step1 raw22361step1Labels := by
      have ha : raw22361step1 = -raw22361step0 := by apply Matrix.ext; change ∀ i j, raw22361step1 i j = -(raw22361step0 i j); unfold raw22361step1 raw22361step0; decide +kernel
      have hl : raw22361step1Labels = raw22361step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3280 node3280Labels := by rfl

def raw22362 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22362Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22362step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22362step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22362step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22362step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw22362step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22362 raw22362Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw22362 raw22362Labels = mixedMoment B raw22362step0 raw22362step0Labels := by
      have hz : ∀ j, raw22362 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22362step0 = (fun i j => raw22362 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22362step0 raw22362; decide +kernel
      have hl : raw22362step0Labels = raw22362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22362 raw22362Labels permutation434 hz
    mixedMoment B raw22362step0 raw22362step0Labels = mixedMoment B raw22362step1 raw22362step1Labels := by
      have hz : ∀ j, raw22362step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22362step1 = (fun i j => raw22362step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22362step1 raw22362step0; decide +kernel
      have hl : raw22362step1Labels = raw22362step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22362step0 raw22362step0Labels permutation56 hz
    mixedMoment B raw22362step1 raw22362step1Labels = mixedMoment B raw22362step2 raw22362step2Labels := by
      have ha : raw22362step2 = (fun i j => raw22362step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22362step2 raw22362step1; decide +kernel
      have hl : raw22362step2Labels = raw22362step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22362step1 raw22362step1Labels permutation9 permutation2
    mixedMoment B raw22362step2 raw22362step2Labels = mixedMoment B raw22362step3 raw22362step3Labels := by
      have ha : raw22362step3 = -raw22362step2 := by apply Matrix.ext; change ∀ i j, raw22362step3 i j = -(raw22362step2 i j); unfold raw22362step3 raw22362step2; decide +kernel
      have hl : raw22362step3Labels = raw22362step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3301 node3301Labels := by rfl

def raw22363 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw22363Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![-1, -1, 2]]
def raw22363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw22363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22363 raw22363Labels = mixedMoment B node2397 node2397Labels := by
  calc
    mixedMoment B raw22363 raw22363Labels = mixedMoment B raw22363step0 raw22363step0Labels := by
      have hz : ∀ j, raw22363 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22363step0 = (fun i j => raw22363 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22363step0 raw22363; decide +kernel
      have hl : raw22363step0Labels = raw22363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22363 raw22363Labels permutation265 hz
    mixedMoment B raw22363step0 raw22363step0Labels = mixedMoment B raw22363step1 raw22363step1Labels := by
      have ha : raw22363step1 = (fun i j => raw22363step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22363step1 raw22363step0; decide +kernel
      have hl : raw22363step1Labels = raw22363step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22363step0 raw22363step0Labels permutation125 permutation2
    _ = mixedMoment B node2397 node2397Labels := by rfl

def raw22364 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw22364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22364 raw22364Labels = mixedMoment B node3284 node3284Labels := by
  calc
    mixedMoment B raw22364 raw22364Labels = mixedMoment B raw22364step0 raw22364step0Labels := by
      have hz : ∀ j, raw22364 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22364step0 = (fun i j => raw22364 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22364step0 raw22364; decide +kernel
      have hl : raw22364step0Labels = raw22364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22364 raw22364Labels permutation265 hz
    mixedMoment B raw22364step0 raw22364step0Labels = mixedMoment B raw22364step1 raw22364step1Labels := by
      have ha : raw22364step1 = -raw22364step0 := by apply Matrix.ext; change ∀ i j, raw22364step1 i j = -(raw22364step0 i j); unfold raw22364step1 raw22364step0; decide +kernel
      have hl : raw22364step1Labels = raw22364step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3284 node3284Labels := by rfl

def raw22365 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22365Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22365step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw22365step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22365step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw22365step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22365 raw22365Labels = mixedMoment B node821 node821Labels := by
  calc
    mixedMoment B raw22365 raw22365Labels = mixedMoment B raw22365step0 raw22365step0Labels := by
      have ha : raw22365step0 = (fun i j => raw22365 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22365step0 raw22365; decide +kernel
      have hl : raw22365step0Labels = raw22365Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22365 raw22365Labels permutation224 permutation4
    mixedMoment B raw22365step0 raw22365step0Labels = mixedMoment B raw22365step1 raw22365step1Labels := by
      have ha : raw22365step1 = -raw22365step0 := by apply Matrix.ext; change ∀ i j, raw22365step1 i j = -(raw22365step0 i j); unfold raw22365step1 raw22365step0; decide +kernel
      have hl : raw22365step1Labels = raw22365step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node821 node821Labels := by rfl

def raw22366 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22366step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw22366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22366step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22366step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22366 raw22366Labels = mixedMoment B node825 node825Labels := by
  calc
    mixedMoment B raw22366 raw22366Labels = mixedMoment B raw22366step0 raw22366step0Labels := by
      have hz : ∀ j, raw22366 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22366step0 = (fun i j => raw22366 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22366step0 raw22366; decide +kernel
      have hl : raw22366step0Labels = raw22366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22366 raw22366Labels permutation265 hz
    mixedMoment B raw22366step0 raw22366step0Labels = mixedMoment B raw22366step1 raw22366step1Labels := by
      have ha : raw22366step1 = (fun i j => raw22366step0 (permutation47 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22366step1 raw22366step0; decide +kernel
      have hl : raw22366step1Labels = raw22366step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22366step0 raw22366step0Labels permutation47 permutation4
    mixedMoment B raw22366step1 raw22366step1Labels = mixedMoment B raw22366step2 raw22366step2Labels := by
      have ha : raw22366step2 = -raw22366step1 := by apply Matrix.ext; change ∀ i j, raw22366step2 i j = -(raw22366step1 i j); unfold raw22366step2 raw22366step1; decide +kernel
      have hl : raw22366step2Labels = raw22366step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node825 node825Labels := by rfl

def raw22367 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![2, -2, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw22367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw22367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22367step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw22367step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22367 raw22367Labels = mixedMoment B node825 node825Labels := by
  calc
    mixedMoment B raw22367 raw22367Labels = mixedMoment B raw22367step0 raw22367step0Labels := by
      have hz : ∀ j, raw22367 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22367step0 = (fun i j => raw22367 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22367step0 raw22367; decide +kernel
      have hl : raw22367step0Labels = raw22367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22367 raw22367Labels permutation265 hz
    mixedMoment B raw22367step0 raw22367step0Labels = mixedMoment B raw22367step1 raw22367step1Labels := by
      have ha : raw22367step1 = (fun i j => raw22367step0 (permutation45 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22367step1 raw22367step0; decide +kernel
      have hl : raw22367step1Labels = raw22367step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22367step0 raw22367step0Labels permutation45 permutation4
    mixedMoment B raw22367step1 raw22367step1Labels = mixedMoment B raw22367step2 raw22367step2Labels := by
      have ha : raw22367step2 = -raw22367step1 := by apply Matrix.ext; change ∀ i j, raw22367step2 i j = -(raw22367step1 i j); unfold raw22367step2 raw22367step1; decide +kernel
      have hl : raw22367step2Labels = raw22367step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node825 node825Labels := by rfl

def raw22368 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22368step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22368step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22368 raw22368Labels = mixedMoment B node848 node848Labels := by
  calc
    mixedMoment B raw22368 raw22368Labels = mixedMoment B raw22368step0 raw22368step0Labels := by
      have hz : ∀ j, raw22368 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22368step0 = (fun i j => raw22368 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22368step0 raw22368; decide +kernel
      have hl : raw22368step0Labels = raw22368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22368 raw22368Labels permutation265 hz
    mixedMoment B raw22368step0 raw22368step0Labels = mixedMoment B raw22368step1 raw22368step1Labels := by
      have ha : raw22368step1 = (fun i j => raw22368step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22368step1 raw22368step0; decide +kernel
      have hl : raw22368step1Labels = raw22368step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22368step0 raw22368step0Labels permutation32 permutation4
    mixedMoment B raw22368step1 raw22368step1Labels = mixedMoment B raw22368step2 raw22368step2Labels := by
      have ha : raw22368step2 = -raw22368step1 := by apply Matrix.ext; change ∀ i j, raw22368step2 i j = -(raw22368step1 i j); unfold raw22368step2 raw22368step1; decide +kernel
      have hl : raw22368step2Labels = raw22368step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node848 node848Labels := by rfl

def raw22369 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw22369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22369step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22369 raw22369Labels = mixedMoment B node823 node823Labels := by
  calc
    mixedMoment B raw22369 raw22369Labels = mixedMoment B raw22369step0 raw22369step0Labels := by
      have hz : ∀ j, raw22369 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22369step0 = (fun i j => raw22369 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22369step0 raw22369; decide +kernel
      have hl : raw22369step0Labels = raw22369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22369 raw22369Labels permutation265 hz
    mixedMoment B raw22369step0 raw22369step0Labels = mixedMoment B raw22369step1 raw22369step1Labels := by
      have ha : raw22369step1 = (fun i j => raw22369step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22369step1 raw22369step0; decide +kernel
      have hl : raw22369step1Labels = raw22369step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22369step0 raw22369step0Labels permutation44 permutation4
    mixedMoment B raw22369step1 raw22369step1Labels = mixedMoment B raw22369step2 raw22369step2Labels := by
      have ha : raw22369step2 = -raw22369step1 := by apply Matrix.ext; change ∀ i j, raw22369step2 i j = -(raw22369step1 i j); unfold raw22369step2 raw22369step1; decide +kernel
      have hl : raw22369step2Labels = raw22369step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node823 node823Labels := by rfl

def raw22370 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22370 raw22370Labels = mixedMoment B node1614 node1614Labels := by
  calc
    mixedMoment B raw22370 raw22370Labels = mixedMoment B raw22370step0 raw22370step0Labels := by
      have ha : raw22370step0 = (fun i j => raw22370 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22370step0 raw22370; decide +kernel
      have hl : raw22370step0Labels = raw22370Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22370 raw22370Labels permutation152 permutation4
    mixedMoment B raw22370step0 raw22370step0Labels = mixedMoment B raw22370step1 raw22370step1Labels := by
      have ha : raw22370step1 = -raw22370step0 := by apply Matrix.ext; change ∀ i j, raw22370step1 i j = -(raw22370step0 i j); unfold raw22370step1 raw22370step0; decide +kernel
      have hl : raw22370step1Labels = raw22370step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1614 node1614Labels := by rfl

def raw22371 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22371step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22371step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw22371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22371step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw22371step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22371 raw22371Labels = mixedMoment B node1751 node1751Labels := by
  calc
    mixedMoment B raw22371 raw22371Labels = mixedMoment B raw22371step0 raw22371step0Labels := by
      have hz : ∀ j, raw22371 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22371step0 = (fun i j => raw22371 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22371step0 raw22371; decide +kernel
      have hl : raw22371step0Labels = raw22371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22371 raw22371Labels permutation434 hz
    mixedMoment B raw22371step0 raw22371step0Labels = mixedMoment B raw22371step1 raw22371step1Labels := by
      have hz : ∀ j, raw22371step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22371step1 = (fun i j => raw22371step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22371step1 raw22371step0; decide +kernel
      have hl : raw22371step1Labels = raw22371step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22371step0 raw22371step0Labels permutation56 hz
    mixedMoment B raw22371step1 raw22371step1Labels = mixedMoment B raw22371step2 raw22371step2Labels := by
      have ha : raw22371step2 = (fun i j => raw22371step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22371step2 raw22371step1; decide +kernel
      have hl : raw22371step2Labels = raw22371step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22371step1 raw22371step1Labels permutation8 permutation4
    mixedMoment B raw22371step2 raw22371step2Labels = mixedMoment B raw22371step3 raw22371step3Labels := by
      have ha : raw22371step3 = -raw22371step2 := by apply Matrix.ext; change ∀ i j, raw22371step3 i j = -(raw22371step2 i j); unfold raw22371step3 raw22371step2; decide +kernel
      have hl : raw22371step3Labels = raw22371step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1751 node1751Labels := by rfl

def raw22372 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw22372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw22372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw22372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22372 raw22372Labels = mixedMoment B node1736 node1736Labels := by
  calc
    mixedMoment B raw22372 raw22372Labels = mixedMoment B raw22372step0 raw22372step0Labels := by
      have hz : ∀ j, raw22372 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22372step0 = (fun i j => raw22372 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22372step0 raw22372; decide +kernel
      have hl : raw22372step0Labels = raw22372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22372 raw22372Labels permutation265 hz
    mixedMoment B raw22372step0 raw22372step0Labels = mixedMoment B raw22372step1 raw22372step1Labels := by
      have ha : raw22372step1 = (fun i j => raw22372step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22372step1 raw22372step0; decide +kernel
      have hl : raw22372step1Labels = raw22372step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22372step0 raw22372step0Labels permutation50 permutation4
    mixedMoment B raw22372step1 raw22372step1Labels = mixedMoment B raw22372step2 raw22372step2Labels := by
      have ha : raw22372step2 = -raw22372step1 := by apply Matrix.ext; change ∀ i j, raw22372step2 i j = -(raw22372step1 i j); unfold raw22372step2 raw22372step1; decide +kernel
      have hl : raw22372step2Labels = raw22372step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1736 node1736Labels := by rfl

def raw22373 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw22373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22373 raw22373Labels = mixedMoment B node1606 node1606Labels := by
  calc
    mixedMoment B raw22373 raw22373Labels = mixedMoment B raw22373step0 raw22373step0Labels := by
      have ha : raw22373step0 = (fun i j => raw22373 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22373step0 raw22373; decide +kernel
      have hl : raw22373step0Labels = raw22373Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22373 raw22373Labels permutation164 permutation4
    mixedMoment B raw22373step0 raw22373step0Labels = mixedMoment B raw22373step1 raw22373step1Labels := by
      have ha : raw22373step1 = -raw22373step0 := by apply Matrix.ext; change ∀ i j, raw22373step1 i j = -(raw22373step0 i j); unfold raw22373step1 raw22373step0; decide +kernel
      have hl : raw22373step1Labels = raw22373step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1606 node1606Labels := by rfl

def raw22374 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw22374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22374step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw22374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22374step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw22374step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22374 raw22374Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw22374 raw22374Labels = mixedMoment B raw22374step0 raw22374step0Labels := by
      have hz : ∀ j, raw22374 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22374step0 = (fun i j => raw22374 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22374step0 raw22374; decide +kernel
      have hl : raw22374step0Labels = raw22374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22374 raw22374Labels permutation434 hz
    mixedMoment B raw22374step0 raw22374step0Labels = mixedMoment B raw22374step1 raw22374step1Labels := by
      have hz : ∀ j, raw22374step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22374step1 = (fun i j => raw22374step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22374step1 raw22374step0; decide +kernel
      have hl : raw22374step1Labels = raw22374step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22374step0 raw22374step0Labels permutation56 hz
    mixedMoment B raw22374step1 raw22374step1Labels = mixedMoment B raw22374step2 raw22374step2Labels := by
      have ha : raw22374step2 = (fun i j => raw22374step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22374step2 raw22374step1; decide +kernel
      have hl : raw22374step2Labels = raw22374step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22374step1 raw22374step1Labels permutation10 permutation4
    mixedMoment B raw22374step2 raw22374step2Labels = mixedMoment B raw22374step3 raw22374step3Labels := by
      have ha : raw22374step3 = -raw22374step2 := by apply Matrix.ext; change ∀ i j, raw22374step3 i j = -(raw22374step2 i j); unfold raw22374step3 raw22374step2; decide +kernel
      have hl : raw22374step3Labels = raw22374step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1738 node1738Labels := by rfl

def raw22375 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw22375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22375step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw22375step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22375step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw22375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22375 raw22375Labels = mixedMoment B node1655 node1655Labels := by
  calc
    mixedMoment B raw22375 raw22375Labels = mixedMoment B raw22375step0 raw22375step0Labels := by
      have hz : ∀ j, raw22375 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22375step0 = (fun i j => raw22375 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22375step0 raw22375; decide +kernel
      have hl : raw22375step0Labels = raw22375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22375 raw22375Labels permutation265 hz
    mixedMoment B raw22375step0 raw22375step0Labels = mixedMoment B raw22375step1 raw22375step1Labels := by
      have ha : raw22375step1 = (fun i j => raw22375step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22375step1 raw22375step0; decide +kernel
      have hl : raw22375step1Labels = raw22375step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22375step0 raw22375step0Labels permutation44 permutation4
    mixedMoment B raw22375step1 raw22375step1Labels = mixedMoment B raw22375step2 raw22375step2Labels := by
      have ha : raw22375step2 = -raw22375step1 := by apply Matrix.ext; change ∀ i j, raw22375step2 i j = -(raw22375step1 i j); unfold raw22375step2 raw22375step1; decide +kernel
      have hl : raw22375step2Labels = raw22375step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1655 node1655Labels := by rfl

def raw22376 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22376Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw22376step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22376step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw22376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22376 raw22376Labels = mixedMoment B node1731 node1731Labels := by
  calc
    mixedMoment B raw22376 raw22376Labels = mixedMoment B raw22376step0 raw22376step0Labels := by
      have ha : raw22376step0 = (fun i j => raw22376 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22376step0 raw22376; decide +kernel
      have hl : raw22376step0Labels = raw22376Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22376 raw22376Labels permutation240 permutation4
    mixedMoment B raw22376step0 raw22376step0Labels = mixedMoment B raw22376step1 raw22376step1Labels := by
      have ha : raw22376step1 = -raw22376step0 := by apply Matrix.ext; change ∀ i j, raw22376step1 i j = -(raw22376step0 i j); unfold raw22376step1 raw22376step0; decide +kernel
      have hl : raw22376step1Labels = raw22376step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1731 node1731Labels := by rfl

def raw22377 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw22377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw22377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22377step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw22377step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22377 raw22377Labels = mixedMoment B node1732 node1732Labels := by
  calc
    mixedMoment B raw22377 raw22377Labels = mixedMoment B raw22377step0 raw22377step0Labels := by
      have hz : ∀ j, raw22377 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22377step0 = (fun i j => raw22377 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22377step0 raw22377; decide +kernel
      have hl : raw22377step0Labels = raw22377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22377 raw22377Labels permutation265 hz
    mixedMoment B raw22377step0 raw22377step0Labels = mixedMoment B raw22377step1 raw22377step1Labels := by
      have ha : raw22377step1 = (fun i j => raw22377step0 (permutation49 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22377step1 raw22377step0; decide +kernel
      have hl : raw22377step1Labels = raw22377step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22377step0 raw22377step0Labels permutation49 permutation4
    mixedMoment B raw22377step1 raw22377step1Labels = mixedMoment B raw22377step2 raw22377step2Labels := by
      have ha : raw22377step2 = -raw22377step1 := by apply Matrix.ext; change ∀ i j, raw22377step2 i j = -(raw22377step1 i j); unfold raw22377step2 raw22377step1; decide +kernel
      have hl : raw22377step2Labels = raw22377step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1732 node1732Labels := by rfl

def raw22378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22378 raw22378Labels = mixedMoment B node1356 node1356Labels := by
  calc
    mixedMoment B raw22378 raw22378Labels = mixedMoment B raw22378step0 raw22378step0Labels := by
      have hz : ∀ j, raw22378 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22378step0 = (fun i j => raw22378 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22378step0 raw22378; decide +kernel
      have hl : raw22378step0Labels = raw22378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22378 raw22378Labels permutation265 hz
    mixedMoment B raw22378step0 raw22378step0Labels = mixedMoment B raw22378step1 raw22378step1Labels := by
      have ha : raw22378step1 = (fun i j => raw22378step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22378step1 raw22378step0; decide +kernel
      have hl : raw22378step1Labels = raw22378step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22378step0 raw22378step0Labels permutation38 permutation2
    _ = mixedMoment B node1356 node1356Labels := by rfl

def raw22379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22379Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22379step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22379 raw22379Labels = mixedMoment B node2970 node2970Labels := by
  calc
    mixedMoment B raw22379 raw22379Labels = mixedMoment B raw22379step0 raw22379step0Labels := by
      have ha : raw22379step0 = (fun i j => raw22379 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22379step0 raw22379; decide +kernel
      have hl : raw22379step0Labels = raw22379Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22379 raw22379Labels permutation158 permutation2
    _ = mixedMoment B node2970 node2970Labels := by rfl

def raw22380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22380Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22380 raw22380Labels = mixedMoment B node2911 node2911Labels := by
  calc
    mixedMoment B raw22380 raw22380Labels = mixedMoment B raw22380step0 raw22380step0Labels := by
      have hz : ∀ j, raw22380 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22380step0 = (fun i j => raw22380 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22380step0 raw22380; decide +kernel
      have hl : raw22380step0Labels = raw22380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22380 raw22380Labels permutation265 hz
    _ = mixedMoment B node2911 node2911Labels := by rfl

def raw22381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw22381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22381 raw22381Labels = mixedMoment B node2856 node2856Labels := by
  calc
    mixedMoment B raw22381 raw22381Labels = mixedMoment B raw22381step0 raw22381step0Labels := by
      have hz : ∀ j, raw22381 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22381step0 = (fun i j => raw22381 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22381step0 raw22381; decide +kernel
      have hl : raw22381step0Labels = raw22381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22381 raw22381Labels permutation265 hz
    mixedMoment B raw22381step0 raw22381step0Labels = mixedMoment B raw22381step1 raw22381step1Labels := by
      have ha : raw22381step1 = (fun i j => raw22381step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22381step1 raw22381step0; decide +kernel
      have hl : raw22381step1Labels = raw22381step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22381step0 raw22381step0Labels permutation38 permutation2
    _ = mixedMoment B node2856 node2856Labels := by rfl

def raw22382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw22382Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw22382step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw22382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22382 raw22382Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw22382 raw22382Labels = mixedMoment B raw22382step0 raw22382step0Labels := by
      have hz : ∀ j, raw22382 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22382step0 = (fun i j => raw22382 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22382step0 raw22382; decide +kernel
      have hl : raw22382step0Labels = raw22382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22382 raw22382Labels permutation265 hz
    mixedMoment B raw22382step0 raw22382step0Labels = mixedMoment B raw22382step1 raw22382step1Labels := by
      have ha : raw22382step1 = (fun i j => raw22382step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22382step1 raw22382step0; decide +kernel
      have hl : raw22382step1Labels = raw22382step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22382step0 raw22382step0Labels permutation38 permutation2
    _ = mixedMoment B node3025 node3025Labels := by rfl

def raw22383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw22383Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -2, 2], ![2, 0, -2], ![1, 1, -2]]
def raw22383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw22383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22383 raw22383Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw22383 raw22383Labels = mixedMoment B raw22383step0 raw22383step0Labels := by
      have hz : ∀ j, raw22383 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22383step0 = (fun i j => raw22383 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22383step0 raw22383; decide +kernel
      have hl : raw22383step0Labels = raw22383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22383 raw22383Labels permutation265 hz
    mixedMoment B raw22383step0 raw22383step0Labels = mixedMoment B raw22383step1 raw22383step1Labels := by
      have ha : raw22383step1 = (fun i j => raw22383step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22383step1 raw22383step0; decide +kernel
      have hl : raw22383step1Labels = raw22383step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22383step0 raw22383step0Labels permutation39 permutation2
    _ = mixedMoment B node3025 node3025Labels := by rfl

def raw22384 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-2, 2], ![2, -2], ![2, -2]]
def raw22384Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22384step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![2, -2], ![2, -2]]
def raw22384step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22384step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw22384step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22384step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw22384step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22384 raw22384Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw22384 raw22384Labels = mixedMoment B raw22384step0 raw22384step0Labels := by
      have hz : ∀ j, raw22384 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22384step0 = (fun i j => raw22384 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22384step0 raw22384; decide +kernel
      have hl : raw22384step0Labels = raw22384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22384 raw22384Labels permutation265 hz
    mixedMoment B raw22384step0 raw22384step0Labels = mixedMoment B raw22384step1 raw22384step1Labels := by
      have ha : raw22384step1 = (fun i j => raw22384step0 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22384step1 raw22384step0; decide +kernel
      have hl : raw22384step1Labels = raw22384step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22384step0 raw22384step0Labels permutation122 permutation0
    mixedMoment B raw22384step1 raw22384step1Labels = mixedMoment B raw22384step2 raw22384step2Labels := by
      have ha : raw22384step2 = -raw22384step1 := by apply Matrix.ext; change ∀ i j, raw22384step2 i j = -(raw22384step1 i j); unfold raw22384step2 raw22384step1; decide +kernel
      have hl : raw22384step2Labels = raw22384step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw22385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22385Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22385 raw22385Labels = mixedMoment B node1377 node1377Labels := by
  calc
    _ = mixedMoment B node1377 node1377Labels := by rfl

def raw22386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22386Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22386 raw22386Labels = mixedMoment B node2913 node2913Labels := by
  calc
    _ = mixedMoment B node2913 node2913Labels := by rfl

def raw22387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22387Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22387step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22387 raw22387Labels = mixedMoment B node2913 node2913Labels := by
  calc
    mixedMoment B raw22387 raw22387Labels = mixedMoment B raw22387step0 raw22387step0Labels := by
      have ha : raw22387step0 = (fun i j => raw22387 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22387step0 raw22387; decide +kernel
      have hl : raw22387step0Labels = raw22387Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22387 raw22387Labels permutation176 permutation2
    _ = mixedMoment B node2913 node2913Labels := by rfl

def raw22388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22388Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw22388step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22388 raw22388Labels = mixedMoment B node2913 node2913Labels := by
  calc
    mixedMoment B raw22388 raw22388Labels = mixedMoment B raw22388step0 raw22388step0Labels := by
      have ha : raw22388step0 = (fun i j => raw22388 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22388step0 raw22388; decide +kernel
      have hl : raw22388step0Labels = raw22388Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22388 raw22388Labels permutation200 permutation2
    _ = mixedMoment B node2913 node2913Labels := by rfl

def raw22389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw22389Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22389 raw22389Labels = mixedMoment B node3059 node3059Labels := by
  calc
    _ = mixedMoment B node3059 node3059Labels := by rfl

def raw22390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw22390Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw22390step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22390 raw22390Labels = mixedMoment B node3059 node3059Labels := by
  calc
    mixedMoment B raw22390 raw22390Labels = mixedMoment B raw22390step0 raw22390step0Labels := by
      have ha : raw22390step0 = (fun i j => raw22390 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22390step0 raw22390; decide +kernel
      have hl : raw22390step0Labels = raw22390Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22390 raw22390Labels permutation153 permutation2
    _ = mixedMoment B node3059 node3059Labels := by rfl

def raw22391 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw22391Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22391step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw22391step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22391step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw22391step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22391 raw22391Labels = mixedMoment B node4087 node4087Labels := by
  calc
    mixedMoment B raw22391 raw22391Labels = mixedMoment B raw22391step0 raw22391step0Labels := by
      have ha : raw22391step0 = (fun i j => raw22391 (permutation569 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22391step0 raw22391; decide +kernel
      have hl : raw22391step0Labels = raw22391Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22391 raw22391Labels permutation569 permutation0
    mixedMoment B raw22391step0 raw22391step0Labels = mixedMoment B raw22391step1 raw22391step1Labels := by
      have ha : raw22391step1 = -raw22391step0 := by apply Matrix.ext; change ∀ i j, raw22391step1 i j = -(raw22391step0 i j); unfold raw22391step1 raw22391step0; decide +kernel
      have hl : raw22391step1Labels = raw22391step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4087 node4087Labels := by rfl

def raw22392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22392Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22392step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22392step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22392 raw22392Labels = mixedMoment B node2522 node2522Labels := by
  calc
    mixedMoment B raw22392 raw22392Labels = mixedMoment B raw22392step0 raw22392step0Labels := by
      have hz : ∀ j, raw22392 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22392step0 = (fun i j => raw22392 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22392step0 raw22392; decide +kernel
      have hl : raw22392step0Labels = raw22392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22392 raw22392Labels permutation434 hz
    mixedMoment B raw22392step0 raw22392step0Labels = mixedMoment B raw22392step1 raw22392step1Labels := by
      have hz : ∀ j, raw22392step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22392step1 = (fun i j => raw22392step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22392step1 raw22392step0; decide +kernel
      have hl : raw22392step1Labels = raw22392step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22392step0 raw22392step0Labels permutation80 hz
    _ = mixedMoment B node2522 node2522Labels := by rfl

def raw22393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22393Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22393step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw22393step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22393 raw22393Labels = mixedMoment B node1245 node1245Labels := by
  calc
    mixedMoment B raw22393 raw22393Labels = mixedMoment B raw22393step0 raw22393step0Labels := by
      have hz : ∀ j, raw22393 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22393step0 = (fun i j => raw22393 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22393step0 raw22393; decide +kernel
      have hl : raw22393step0Labels = raw22393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22393 raw22393Labels permutation434 hz
    mixedMoment B raw22393step0 raw22393step0Labels = mixedMoment B raw22393step1 raw22393step1Labels := by
      have hz : ∀ j, raw22393step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22393step1 = (fun i j => raw22393step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22393step1 raw22393step0; decide +kernel
      have hl : raw22393step1Labels = raw22393step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22393step0 raw22393step0Labels permutation80 hz
    _ = mixedMoment B node1245 node1245Labels := by rfl

def raw22394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22394Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22394step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22394 raw22394Labels = mixedMoment B node1133 node1133Labels := by
  calc
    mixedMoment B raw22394 raw22394Labels = mixedMoment B raw22394step0 raw22394step0Labels := by
      have hz : ∀ j, raw22394 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22394step0 = (fun i j => raw22394 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22394step0 raw22394; decide +kernel
      have hl : raw22394step0Labels = raw22394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22394 raw22394Labels permutation434 hz
    _ = mixedMoment B node1133 node1133Labels := by rfl

def raw22395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22395Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw22395step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22395 raw22395Labels = mixedMoment B node1133 node1133Labels := by
  calc
    mixedMoment B raw22395 raw22395Labels = mixedMoment B raw22395step0 raw22395step0Labels := by
      have hz : ∀ j, raw22395 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22395step0 = (fun i j => raw22395 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22395step0 raw22395; decide +kernel
      have hl : raw22395step0Labels = raw22395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22395 raw22395Labels permutation346 hz
    _ = mixedMoment B node1133 node1133Labels := by rfl

def raw22396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 1, -3]]
def raw22396Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0], ![2, 1, -3]]
def raw22396step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22396step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![3, -3, 0], ![2, 1, -3]]
def raw22396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22396step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 1, -3], ![3, -3, 0]]
def raw22396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22396 raw22396Labels = mixedMoment B node1146 node1146Labels := by
  calc
    mixedMoment B raw22396 raw22396Labels = mixedMoment B raw22396step0 raw22396step0Labels := by
      have hz : ∀ j, raw22396 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22396step0 = (fun i j => raw22396 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22396step0 raw22396; decide +kernel
      have hl : raw22396step0Labels = raw22396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22396 raw22396Labels permutation434 hz
    mixedMoment B raw22396step0 raw22396step0Labels = mixedMoment B raw22396step1 raw22396step1Labels := by
      have hz : ∀ j, raw22396step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22396step1 = (fun i j => raw22396step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22396step1 raw22396step0; decide +kernel
      have hl : raw22396step1Labels = raw22396step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22396step0 raw22396step0Labels permutation80 hz
    mixedMoment B raw22396step1 raw22396step1Labels = mixedMoment B raw22396step2 raw22396step2Labels := by
      have ha : raw22396step2 = (fun i j => raw22396step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22396step2 raw22396step1; decide +kernel
      have hl : raw22396step2Labels = raw22396step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22396step1 raw22396step1Labels permutation9 permutation2
    _ = mixedMoment B node1146 node1146Labels := by rfl

def raw22397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22397Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw22397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw22397step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22397 raw22397Labels = mixedMoment B node1143 node1143Labels := by
  calc
    mixedMoment B raw22397 raw22397Labels = mixedMoment B raw22397step0 raw22397step0Labels := by
      have hz : ∀ j, raw22397 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22397step0 = (fun i j => raw22397 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22397step0 raw22397; decide +kernel
      have hl : raw22397step0Labels = raw22397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22397 raw22397Labels permutation434 hz
    mixedMoment B raw22397step0 raw22397step0Labels = mixedMoment B raw22397step1 raw22397step1Labels := by
      have hz : ∀ j, raw22397step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22397step1 = (fun i j => raw22397step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22397step1 raw22397step0; decide +kernel
      have hl : raw22397step1Labels = raw22397step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22397step0 raw22397step0Labels permutation80 hz
    _ = mixedMoment B node1143 node1143Labels := by rfl

def raw22398 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![0, 0], ![3, -3]]
def raw22398Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22398step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![0, 0], ![3, -3]]
def raw22398step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22398step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![3, -3]]
def raw22398step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22398step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw22398step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22398step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw22398step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22398step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw22398step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22398 raw22398Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw22398 raw22398Labels = mixedMoment B raw22398step0 raw22398step0Labels := by
      have hz : ∀ j, raw22398 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22398step0 = (fun i j => raw22398 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22398step0 raw22398; decide +kernel
      have hl : raw22398step0Labels = raw22398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22398 raw22398Labels permutation520 hz
    mixedMoment B raw22398step0 raw22398step0Labels = mixedMoment B raw22398step1 raw22398step1Labels := by
      have hz : ∀ j, raw22398step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22398step1 = (fun i j => raw22398step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22398step1 raw22398step0; decide +kernel
      have hl : raw22398step1Labels = raw22398step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22398step0 raw22398step0Labels permutation104 hz
    mixedMoment B raw22398step1 raw22398step1Labels = mixedMoment B raw22398step2 raw22398step2Labels := by
      have hz : ∀ j, raw22398step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw22398step2 = (fun i j => raw22398step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw22398step2 raw22398step1; decide +kernel
      have hl : raw22398step2Labels = raw22398step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22398step1 raw22398step1Labels permutation20 hz
    mixedMoment B raw22398step2 raw22398step2Labels = mixedMoment B raw22398step3 raw22398step3Labels := by
      have ha : raw22398step3 = (fun i j => raw22398step2 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22398step3 raw22398step2; decide +kernel
      have hl : raw22398step3Labels = raw22398step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22398step2 raw22398step2Labels permutation7 permutation0
    mixedMoment B raw22398step3 raw22398step3Labels = mixedMoment B raw22398step4 raw22398step4Labels := by
      have ha : raw22398step4 = -raw22398step3 := by apply Matrix.ext; change ∀ i j, raw22398step4 i j = -(raw22398step3 i j); unfold raw22398step4 raw22398step3; decide +kernel
      have hl : raw22398step4Labels = raw22398step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw22399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22399Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -3, 1]]
def raw22399step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22399step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, 0, -2], ![2, -3, 1]]
def raw22399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22399step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw22399step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22399 raw22399Labels = mixedMoment B node653 node653Labels := by
  calc
    mixedMoment B raw22399 raw22399Labels = mixedMoment B raw22399step0 raw22399step0Labels := by
      have hz : ∀ j, raw22399 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22399step0 = (fun i j => raw22399 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22399step0 raw22399; decide +kernel
      have hl : raw22399step0Labels = raw22399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22399 raw22399Labels permutation434 hz
    mixedMoment B raw22399step0 raw22399step0Labels = mixedMoment B raw22399step1 raw22399step1Labels := by
      have hz : ∀ j, raw22399step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw22399step1 = (fun i j => raw22399step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw22399step1 raw22399step0; decide +kernel
      have hl : raw22399step1Labels = raw22399step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22399step0 raw22399step0Labels permutation80 hz
    mixedMoment B raw22399step1 raw22399step1Labels = mixedMoment B raw22399step2 raw22399step2Labels := by
      have ha : raw22399step2 = (fun i j => raw22399step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22399step2 raw22399step1; decide +kernel
      have hl : raw22399step2Labels = raw22399step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22399step1 raw22399step1Labels permutation9 permutation2
    _ = mixedMoment B node653 node653Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
