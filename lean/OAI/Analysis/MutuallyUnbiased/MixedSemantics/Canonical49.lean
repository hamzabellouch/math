import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw6272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![1, 1, -2]]
def raw6272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![1, 1, -2]]
def raw6272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw6272step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw6272step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6272 raw6272Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw6272 raw6272Labels = mixedMoment B raw6272step0 raw6272step0Labels := by
      have hz : ∀ j, raw6272 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6272step0 = (fun i j => raw6272 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6272step0 raw6272; decide +kernel
      have hl : raw6272step0Labels = raw6272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6272 raw6272Labels permutation346 hz
    mixedMoment B raw6272step0 raw6272step0Labels = mixedMoment B raw6272step1 raw6272step1Labels := by
      have ha : raw6272step1 = (fun i j => raw6272step0 (permutation121 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6272step1 raw6272step0; decide +kernel
      have hl : raw6272step1Labels = raw6272step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6272step0 raw6272step0Labels permutation121 permutation5
    mixedMoment B raw6272step1 raw6272step1Labels = mixedMoment B raw6272step2 raw6272step2Labels := by
      have ha : raw6272step2 = raw6272step1 := by apply Matrix.ext; unfold raw6272step2 raw6272step1; decide +kernel
      have hl : raw6272step1Labels = labelEmbedding8 ∘ raw6272step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6272step1 raw6272step1Labels raw6272step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5161 node5161Labels := by rfl

def raw6273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw6273step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw6273step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6273 raw6273Labels = mixedMoment B node4402 node4402Labels := by
  calc
    mixedMoment B raw6273 raw6273Labels = mixedMoment B raw6273step0 raw6273step0Labels := by
      have hz : ∀ j, raw6273 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6273step0 = (fun i j => raw6273 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6273step0 raw6273; decide +kernel
      have hl : raw6273step0Labels = raw6273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6273 raw6273Labels permutation346 hz
    mixedMoment B raw6273step0 raw6273step0Labels = mixedMoment B raw6273step1 raw6273step1Labels := by
      have ha : raw6273step1 = (fun i j => raw6273step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6273step1 raw6273step0; decide +kernel
      have hl : raw6273step1Labels = raw6273step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6273step0 raw6273step0Labels permutation32 permutation3
    mixedMoment B raw6273step1 raw6273step1Labels = mixedMoment B raw6273step2 raw6273step2Labels := by
      have ha : raw6273step2 = raw6273step1 := by apply Matrix.ext; unfold raw6273step2 raw6273step1; decide +kernel
      have hl : raw6273step1Labels = labelEmbedding6 ∘ raw6273step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6273step1 raw6273step1Labels raw6273step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4402 node4402Labels := by rfl

def raw6274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6274step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw6274step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6274step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw6274step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6274 raw6274Labels = mixedMoment B node5001 node5001Labels := by
  calc
    mixedMoment B raw6274 raw6274Labels = mixedMoment B raw6274step0 raw6274step0Labels := by
      have hz : ∀ j, raw6274 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6274step0 = (fun i j => raw6274 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6274step0 raw6274; decide +kernel
      have hl : raw6274step0Labels = raw6274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6274 raw6274Labels permutation346 hz
    mixedMoment B raw6274step0 raw6274step0Labels = mixedMoment B raw6274step1 raw6274step1Labels := by
      have ha : raw6274step1 = (fun i j => raw6274step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6274step1 raw6274step0; decide +kernel
      have hl : raw6274step1Labels = raw6274step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6274step0 raw6274step0Labels permutation32 permutation3
    mixedMoment B raw6274step1 raw6274step1Labels = mixedMoment B raw6274step2 raw6274step2Labels := by
      have ha : raw6274step2 = raw6274step1 := by apply Matrix.ext; unfold raw6274step2 raw6274step1; decide +kernel
      have hl : raw6274step1Labels = labelEmbedding6 ∘ raw6274step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6274step1 raw6274step1Labels raw6274step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5001 node5001Labels := by rfl

def raw6275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw6275step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6275step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw6275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6275 raw6275Labels = mixedMoment B node5048 node5048Labels := by
  calc
    mixedMoment B raw6275 raw6275Labels = mixedMoment B raw6275step0 raw6275step0Labels := by
      have ha : raw6275step0 = (fun i j => raw6275 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6275step0 raw6275; decide +kernel
      have hl : raw6275step0Labels = raw6275Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6275 raw6275Labels permutation176 permutation3
    mixedMoment B raw6275step0 raw6275step0Labels = mixedMoment B raw6275step1 raw6275step1Labels := by
      have ha : raw6275step1 = raw6275step0 := by apply Matrix.ext; unfold raw6275step1 raw6275step0; decide +kernel
      have hl : raw6275step0Labels = labelEmbedding6 ∘ raw6275step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6275step0 raw6275step0Labels raw6275step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5048 node5048Labels := by rfl

def raw6276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw6276step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw6276step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6276 raw6276Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw6276 raw6276Labels = mixedMoment B raw6276step0 raw6276step0Labels := by
      have hz : ∀ j, raw6276 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6276step0 = (fun i j => raw6276 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6276step0 raw6276; decide +kernel
      have hl : raw6276step0Labels = raw6276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6276 raw6276Labels permutation346 hz
    mixedMoment B raw6276step0 raw6276step0Labels = mixedMoment B raw6276step1 raw6276step1Labels := by
      have ha : raw6276step1 = (fun i j => raw6276step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6276step1 raw6276step0; decide +kernel
      have hl : raw6276step1Labels = raw6276step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6276step0 raw6276step0Labels permutation38 permutation3
    mixedMoment B raw6276step1 raw6276step1Labels = mixedMoment B raw6276step2 raw6276step2Labels := by
      have ha : raw6276step2 = raw6276step1 := by apply Matrix.ext; unfold raw6276step2 raw6276step1; decide +kernel
      have hl : raw6276step1Labels = labelEmbedding6 ∘ raw6276step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6276step1 raw6276step1Labels raw6276step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5139 node5139Labels := by rfl

def raw6277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw6277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw6277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw6277step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw6277step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6277 raw6277Labels = mixedMoment B node5252 node5252Labels := by
  calc
    mixedMoment B raw6277 raw6277Labels = mixedMoment B raw6277step0 raw6277step0Labels := by
      have hz : ∀ j, raw6277 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6277step0 = (fun i j => raw6277 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6277step0 raw6277; decide +kernel
      have hl : raw6277step0Labels = raw6277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6277 raw6277Labels permutation346 hz
    mixedMoment B raw6277step0 raw6277step0Labels = mixedMoment B raw6277step1 raw6277step1Labels := by
      have ha : raw6277step1 = (fun i j => raw6277step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6277step1 raw6277step0; decide +kernel
      have hl : raw6277step1Labels = raw6277step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6277step0 raw6277step0Labels permutation137 permutation2
    mixedMoment B raw6277step1 raw6277step1Labels = mixedMoment B raw6277step2 raw6277step2Labels := by
      have ha : raw6277step2 = -raw6277step1 := by apply Matrix.ext; change ∀ i j, raw6277step2 i j = -(raw6277step1 i j); unfold raw6277step2 raw6277step1; decide +kernel
      have hl : raw6277step2Labels = raw6277step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5252 node5252Labels := by rfl

def raw6278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6278Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6278step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6278step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6278 raw6278Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw6278 raw6278Labels = mixedMoment B raw6278step0 raw6278step0Labels := by
      have hz : ∀ j, raw6278 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6278step0 = (fun i j => raw6278 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6278step0 raw6278; decide +kernel
      have hl : raw6278step0Labels = raw6278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6278 raw6278Labels permutation346 hz
    mixedMoment B raw6278step0 raw6278step0Labels = mixedMoment B raw6278step1 raw6278step1Labels := by
      have ha : raw6278step1 = (fun i j => raw6278step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6278step1 raw6278step0; decide +kernel
      have hl : raw6278step1Labels = raw6278step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6278step0 raw6278step0Labels permutation32 permutation3
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw6279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6279Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6279 raw6279Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw6279 raw6279Labels = mixedMoment B raw6279step0 raw6279step0Labels := by
      have ha : raw6279step0 = (fun i j => raw6279 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6279step0 raw6279; decide +kernel
      have hl : raw6279step0Labels = raw6279Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6279 raw6279Labels permutation176 permutation3
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw6280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6280Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6280step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw6280step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6280 raw6280Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw6280 raw6280Labels = mixedMoment B raw6280step0 raw6280step0Labels := by
      have hz : ∀ j, raw6280 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6280step0 = (fun i j => raw6280 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6280step0 raw6280; decide +kernel
      have hl : raw6280step0Labels = raw6280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6280 raw6280Labels permutation346 hz
    mixedMoment B raw6280step0 raw6280step0Labels = mixedMoment B raw6280step1 raw6280step1Labels := by
      have ha : raw6280step1 = (fun i j => raw6280step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6280step1 raw6280step0; decide +kernel
      have hl : raw6280step1Labels = raw6280step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6280step0 raw6280step0Labels permutation38 permutation3
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw6281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6281Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6281step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw6281step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6281 raw6281Labels = mixedMoment B node4012 node4012Labels := by
  calc
    mixedMoment B raw6281 raw6281Labels = mixedMoment B raw6281step0 raw6281step0Labels := by
      have hz : ∀ j, raw6281 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6281step0 = (fun i j => raw6281 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6281step0 raw6281; decide +kernel
      have hl : raw6281step0Labels = raw6281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6281 raw6281Labels permutation346 hz
    mixedMoment B raw6281step0 raw6281step0Labels = mixedMoment B raw6281step1 raw6281step1Labels := by
      have ha : raw6281step1 = (fun i j => raw6281step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6281step1 raw6281step0; decide +kernel
      have hl : raw6281step1Labels = raw6281step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6281step0 raw6281step0Labels permutation32 permutation3
    _ = mixedMoment B node4012 node4012Labels := by rfl

def raw6282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6282Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6282step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw6282step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6282 raw6282Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw6282 raw6282Labels = mixedMoment B raw6282step0 raw6282step0Labels := by
      have hz : ∀ j, raw6282 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6282step0 = (fun i j => raw6282 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6282step0 raw6282; decide +kernel
      have hl : raw6282step0Labels = raw6282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6282 raw6282Labels permutation346 hz
    mixedMoment B raw6282step0 raw6282step0Labels = mixedMoment B raw6282step1 raw6282step1Labels := by
      have ha : raw6282step1 = (fun i j => raw6282step0 (permutation134 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6282step1 raw6282step0; decide +kernel
      have hl : raw6282step1Labels = raw6282step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6282step0 raw6282step0Labels permutation134 permutation6
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw6283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6283Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6283step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6283step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6283 raw6283Labels = mixedMoment B node1042 node1042Labels := by
  calc
    mixedMoment B raw6283 raw6283Labels = mixedMoment B raw6283step0 raw6283step0Labels := by
      have hz : ∀ j, raw6283 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6283step0 = (fun i j => raw6283 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6283step0 raw6283; decide +kernel
      have hl : raw6283step0Labels = raw6283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6283 raw6283Labels permutation346 hz
    mixedMoment B raw6283step0 raw6283step0Labels = mixedMoment B raw6283step1 raw6283step1Labels := by
      have ha : raw6283step1 = (fun i j => raw6283step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6283step1 raw6283step0; decide +kernel
      have hl : raw6283step1Labels = raw6283step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6283step0 raw6283step0Labels permutation38 permutation3
    _ = mixedMoment B node1042 node1042Labels := by rfl

def raw6284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6284Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6284step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6284 raw6284Labels = mixedMoment B node2481 node2481Labels := by
  calc
    mixedMoment B raw6284 raw6284Labels = mixedMoment B raw6284step0 raw6284step0Labels := by
      have ha : raw6284step0 = (fun i j => raw6284 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6284step0 raw6284; decide +kernel
      have hl : raw6284step0Labels = raw6284Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6284 raw6284Labels permutation182 permutation3
    _ = mixedMoment B node2481 node2481Labels := by rfl

def raw6285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6285Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6285step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw6285step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6285 raw6285Labels = mixedMoment B node2596 node2596Labels := by
  calc
    mixedMoment B raw6285 raw6285Labels = mixedMoment B raw6285step0 raw6285step0Labels := by
      have hz : ∀ j, raw6285 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6285step0 = (fun i j => raw6285 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6285step0 raw6285; decide +kernel
      have hl : raw6285step0Labels = raw6285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6285 raw6285Labels permutation346 hz
    mixedMoment B raw6285step0 raw6285step0Labels = mixedMoment B raw6285step1 raw6285step1Labels := by
      have ha : raw6285step1 = (fun i j => raw6285step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6285step1 raw6285step0; decide +kernel
      have hl : raw6285step1Labels = raw6285step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6285step0 raw6285step0Labels permutation38 permutation3
    _ = mixedMoment B node2596 node2596Labels := by rfl

def raw6286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6286Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6286step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6286step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw6286step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6286 raw6286Labels = mixedMoment B node2753 node2753Labels := by
  calc
    mixedMoment B raw6286 raw6286Labels = mixedMoment B raw6286step0 raw6286step0Labels := by
      have hz : ∀ j, raw6286 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6286step0 = (fun i j => raw6286 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6286step0 raw6286; decide +kernel
      have hl : raw6286step0Labels = raw6286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6286 raw6286Labels permutation346 hz
    mixedMoment B raw6286step0 raw6286step0Labels = mixedMoment B raw6286step1 raw6286step1Labels := by
      have ha : raw6286step1 = (fun i j => raw6286step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6286step1 raw6286step0; decide +kernel
      have hl : raw6286step1Labels = raw6286step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6286step0 raw6286step0Labels permutation40 permutation3
    _ = mixedMoment B node2753 node2753Labels := by rfl

def raw6287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6287Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6287step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6287step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6287 raw6287Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw6287 raw6287Labels = mixedMoment B raw6287step0 raw6287step0Labels := by
      have hz : ∀ j, raw6287 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6287step0 = (fun i j => raw6287 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6287step0 raw6287; decide +kernel
      have hl : raw6287step0Labels = raw6287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6287 raw6287Labels permutation346 hz
    mixedMoment B raw6287step0 raw6287step0Labels = mixedMoment B raw6287step1 raw6287step1Labels := by
      have ha : raw6287step1 = (fun i j => raw6287step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6287step1 raw6287step0; decide +kernel
      have hl : raw6287step1Labels = raw6287step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6287step0 raw6287step0Labels permutation42 permutation3
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw6288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6288Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6288step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6288 raw6288Labels = mixedMoment B node981 node981Labels := by
  calc
    mixedMoment B raw6288 raw6288Labels = mixedMoment B raw6288step0 raw6288step0Labels := by
      have ha : raw6288step0 = (fun i j => raw6288 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6288step0 raw6288; decide +kernel
      have hl : raw6288step0Labels = raw6288Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6288 raw6288Labels permutation158 permutation3
    _ = mixedMoment B node981 node981Labels := by rfl

def raw6289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6289Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6289step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6289 raw6289Labels = mixedMoment B node2384 node2384Labels := by
  calc
    mixedMoment B raw6289 raw6289Labels = mixedMoment B raw6289step0 raw6289step0Labels := by
      have ha : raw6289step0 = (fun i j => raw6289 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6289step0 raw6289; decide +kernel
      have hl : raw6289step0Labels = raw6289Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6289 raw6289Labels permutation158 permutation3
    _ = mixedMoment B node2384 node2384Labels := by rfl

def raw6290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6290Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6290step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6290 raw6290Labels = mixedMoment B node2557 node2557Labels := by
  calc
    mixedMoment B raw6290 raw6290Labels = mixedMoment B raw6290step0 raw6290step0Labels := by
      have ha : raw6290step0 = (fun i j => raw6290 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6290step0 raw6290; decide +kernel
      have hl : raw6290step0Labels = raw6290Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6290 raw6290Labels permutation200 permutation3
    _ = mixedMoment B node2557 node2557Labels := by rfl

def raw6291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6291Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6291step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6291 raw6291Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw6291 raw6291Labels = mixedMoment B raw6291step0 raw6291step0Labels := by
      have ha : raw6291step0 = (fun i j => raw6291 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6291step0 raw6291; decide +kernel
      have hl : raw6291step0Labels = raw6291Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6291 raw6291Labels permutation160 permutation3
    _ = mixedMoment B node2710 node2710Labels := by rfl

def raw6292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6292Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw6292step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6292 raw6292Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw6292 raw6292Labels = mixedMoment B raw6292step0 raw6292step0Labels := by
      have ha : raw6292step0 = (fun i j => raw6292 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6292step0 raw6292; decide +kernel
      have hl : raw6292step0Labels = raw6292Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6292 raw6292Labels permutation162 permutation3
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw6293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6293Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6293step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6293step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6293 raw6293Labels = mixedMoment B node1008 node1008Labels := by
  calc
    mixedMoment B raw6293 raw6293Labels = mixedMoment B raw6293step0 raw6293step0Labels := by
      have hz : ∀ j, raw6293 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6293step0 = (fun i j => raw6293 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6293step0 raw6293; decide +kernel
      have hl : raw6293step0Labels = raw6293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6293 raw6293Labels permutation346 hz
    mixedMoment B raw6293step0 raw6293step0Labels = mixedMoment B raw6293step1 raw6293step1Labels := by
      have ha : raw6293step1 = (fun i j => raw6293step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6293step1 raw6293step0; decide +kernel
      have hl : raw6293step1Labels = raw6293step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6293step0 raw6293step0Labels permutation32 permutation3
    _ = mixedMoment B node1008 node1008Labels := by rfl

def raw6294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6294Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6294step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6294step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6294 raw6294Labels = mixedMoment B node2406 node2406Labels := by
  calc
    mixedMoment B raw6294 raw6294Labels = mixedMoment B raw6294step0 raw6294step0Labels := by
      have hz : ∀ j, raw6294 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6294step0 = (fun i j => raw6294 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6294step0 raw6294; decide +kernel
      have hl : raw6294step0Labels = raw6294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6294 raw6294Labels permutation346 hz
    mixedMoment B raw6294step0 raw6294step0Labels = mixedMoment B raw6294step1 raw6294step1Labels := by
      have ha : raw6294step1 = (fun i j => raw6294step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6294step1 raw6294step0; decide +kernel
      have hl : raw6294step1Labels = raw6294step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6294step0 raw6294step0Labels permutation32 permutation3
    _ = mixedMoment B node2406 node2406Labels := by rfl

def raw6295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6295step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6295 raw6295Labels = mixedMoment B node2464 node2464Labels := by
  calc
    mixedMoment B raw6295 raw6295Labels = mixedMoment B raw6295step0 raw6295step0Labels := by
      have ha : raw6295step0 = (fun i j => raw6295 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6295step0 raw6295; decide +kernel
      have hl : raw6295step0Labels = raw6295Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6295 raw6295Labels permutation176 permutation3
    _ = mixedMoment B node2464 node2464Labels := by rfl

def raw6296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6296step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6296 raw6296Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw6296 raw6296Labels = mixedMoment B raw6296step0 raw6296step0Labels := by
      have hz : ∀ j, raw6296 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6296step0 = (fun i j => raw6296 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6296step0 raw6296; decide +kernel
      have hl : raw6296step0Labels = raw6296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6296 raw6296Labels permutation346 hz
    mixedMoment B raw6296step0 raw6296step0Labels = mixedMoment B raw6296step1 raw6296step1Labels := by
      have ha : raw6296step1 = (fun i j => raw6296step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6296step1 raw6296step0; decide +kernel
      have hl : raw6296step1Labels = raw6296step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6296step0 raw6296step0Labels permutation34 permutation3
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw6297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6297step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw6297step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6297 raw6297Labels = mixedMoment B node2736 node2736Labels := by
  calc
    mixedMoment B raw6297 raw6297Labels = mixedMoment B raw6297step0 raw6297step0Labels := by
      have hz : ∀ j, raw6297 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6297step0 = (fun i j => raw6297 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6297step0 raw6297; decide +kernel
      have hl : raw6297step0Labels = raw6297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6297 raw6297Labels permutation346 hz
    mixedMoment B raw6297step0 raw6297step0Labels = mixedMoment B raw6297step1 raw6297step1Labels := by
      have ha : raw6297step1 = (fun i j => raw6297step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6297step1 raw6297step0; decide +kernel
      have hl : raw6297step1Labels = raw6297step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6297step0 raw6297step0Labels permutation36 permutation3
    _ = mixedMoment B node2736 node2736Labels := by rfl

def raw6298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6298step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw6298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6298 raw6298Labels = mixedMoment B node984 node984Labels := by
  calc
    mixedMoment B raw6298 raw6298Labels = mixedMoment B raw6298step0 raw6298step0Labels := by
      have hz : ∀ j, raw6298 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6298step0 = (fun i j => raw6298 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6298step0 raw6298; decide +kernel
      have hl : raw6298step0Labels = raw6298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6298 raw6298Labels permutation346 hz
    mixedMoment B raw6298step0 raw6298step0Labels = mixedMoment B raw6298step1 raw6298step1Labels := by
      have ha : raw6298step1 = (fun i j => raw6298step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6298step1 raw6298step0; decide +kernel
      have hl : raw6298step1Labels = raw6298step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6298step0 raw6298step0Labels permutation33 permutation3
    _ = mixedMoment B node984 node984Labels := by rfl

def raw6299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6299step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw6299step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6299 raw6299Labels = mixedMoment B node2387 node2387Labels := by
  calc
    mixedMoment B raw6299 raw6299Labels = mixedMoment B raw6299step0 raw6299step0Labels := by
      have hz : ∀ j, raw6299 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6299step0 = (fun i j => raw6299 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6299step0 raw6299; decide +kernel
      have hl : raw6299step0Labels = raw6299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6299 raw6299Labels permutation346 hz
    mixedMoment B raw6299step0 raw6299step0Labels = mixedMoment B raw6299step1 raw6299step1Labels := by
      have ha : raw6299step1 = (fun i j => raw6299step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6299step1 raw6299step0; decide +kernel
      have hl : raw6299step1Labels = raw6299step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6299step0 raw6299step0Labels permutation33 permutation3
    _ = mixedMoment B node2387 node2387Labels := by rfl

def raw6300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6300Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw6300step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6300 raw6300Labels = mixedMoment B node2451 node2451Labels := by
  calc
    mixedMoment B raw6300 raw6300Labels = mixedMoment B raw6300step0 raw6300step0Labels := by
      have ha : raw6300step0 = (fun i j => raw6300 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6300step0 raw6300; decide +kernel
      have hl : raw6300step0Labels = raw6300Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6300 raw6300Labels permutation177 permutation3
    _ = mixedMoment B node2451 node2451Labels := by rfl

def raw6301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw6301step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6301 raw6301Labels = mixedMoment B node2560 node2560Labels := by
  calc
    mixedMoment B raw6301 raw6301Labels = mixedMoment B raw6301step0 raw6301step0Labels := by
      have hz : ∀ j, raw6301 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6301step0 = (fun i j => raw6301 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6301step0 raw6301; decide +kernel
      have hl : raw6301step0Labels = raw6301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6301 raw6301Labels permutation346 hz
    mixedMoment B raw6301step0 raw6301step0Labels = mixedMoment B raw6301step1 raw6301step1Labels := by
      have ha : raw6301step1 = (fun i j => raw6301step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6301step1 raw6301step0; decide +kernel
      have hl : raw6301step1Labels = raw6301step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6301step0 raw6301step0Labels permutation39 permutation3
    _ = mixedMoment B node2560 node2560Labels := by rfl

def raw6302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![1, 1, -2]]
def raw6302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![1, 1, -2]]
def raw6302step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw6302step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6302 raw6302Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw6302 raw6302Labels = mixedMoment B raw6302step0 raw6302step0Labels := by
      have hz : ∀ j, raw6302 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6302step0 = (fun i j => raw6302 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6302step0 raw6302; decide +kernel
      have hl : raw6302step0Labels = raw6302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6302 raw6302Labels permutation346 hz
    mixedMoment B raw6302step0 raw6302step0Labels = mixedMoment B raw6302step1 raw6302step1Labels := by
      have ha : raw6302step1 = (fun i j => raw6302step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6302step1 raw6302step0; decide +kernel
      have hl : raw6302step1Labels = raw6302step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6302step0 raw6302step0Labels permutation33 permutation3
    _ = mixedMoment B node2719 node2719Labels := by rfl

def raw6303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6303step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw6303step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6303 raw6303Labels = mixedMoment B node983 node983Labels := by
  calc
    mixedMoment B raw6303 raw6303Labels = mixedMoment B raw6303step0 raw6303step0Labels := by
      have hz : ∀ j, raw6303 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6303step0 = (fun i j => raw6303 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6303step0 raw6303; decide +kernel
      have hl : raw6303step0Labels = raw6303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6303 raw6303Labels permutation346 hz
    mixedMoment B raw6303step0 raw6303step0Labels = mixedMoment B raw6303step1 raw6303step1Labels := by
      have ha : raw6303step1 = (fun i j => raw6303step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6303step1 raw6303step0; decide +kernel
      have hl : raw6303step1Labels = raw6303step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6303step0 raw6303step0Labels permutation32 permutation3
    _ = mixedMoment B node983 node983Labels := by rfl

def raw6304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6304Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6304step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw6304step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6304 raw6304Labels = mixedMoment B node2386 node2386Labels := by
  calc
    mixedMoment B raw6304 raw6304Labels = mixedMoment B raw6304step0 raw6304step0Labels := by
      have hz : ∀ j, raw6304 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6304step0 = (fun i j => raw6304 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6304step0 raw6304; decide +kernel
      have hl : raw6304step0Labels = raw6304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6304 raw6304Labels permutation346 hz
    mixedMoment B raw6304step0 raw6304step0Labels = mixedMoment B raw6304step1 raw6304step1Labels := by
      have ha : raw6304step1 = (fun i j => raw6304step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6304step1 raw6304step0; decide +kernel
      have hl : raw6304step1Labels = raw6304step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6304step0 raw6304step0Labels permutation32 permutation3
    _ = mixedMoment B node2386 node2386Labels := by rfl

def raw6305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6305Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw6305step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6305 raw6305Labels = mixedMoment B node2450 node2450Labels := by
  calc
    mixedMoment B raw6305 raw6305Labels = mixedMoment B raw6305step0 raw6305step0Labels := by
      have ha : raw6305step0 = (fun i j => raw6305 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6305step0 raw6305; decide +kernel
      have hl : raw6305step0Labels = raw6305Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6305 raw6305Labels permutation176 permutation3
    _ = mixedMoment B node2450 node2450Labels := by rfl

def raw6306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6306Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6306step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw6306step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6306 raw6306Labels = mixedMoment B node2558 node2558Labels := by
  calc
    mixedMoment B raw6306 raw6306Labels = mixedMoment B raw6306step0 raw6306step0Labels := by
      have hz : ∀ j, raw6306 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6306step0 = (fun i j => raw6306 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6306step0 raw6306; decide +kernel
      have hl : raw6306step0Labels = raw6306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6306 raw6306Labels permutation346 hz
    mixedMoment B raw6306step0 raw6306step0Labels = mixedMoment B raw6306step1 raw6306step1Labels := by
      have ha : raw6306step1 = (fun i j => raw6306step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6306step1 raw6306step0; decide +kernel
      have hl : raw6306step1Labels = raw6306step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6306step0 raw6306step0Labels permutation38 permutation3
    _ = mixedMoment B node2558 node2558Labels := by rfl

def raw6307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw6307Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw6307step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw6307step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6307 raw6307Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw6307 raw6307Labels = mixedMoment B raw6307step0 raw6307step0Labels := by
      have hz : ∀ j, raw6307 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6307step0 = (fun i j => raw6307 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6307step0 raw6307; decide +kernel
      have hl : raw6307step0Labels = raw6307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6307 raw6307Labels permutation346 hz
    mixedMoment B raw6307step0 raw6307step0Labels = mixedMoment B raw6307step1 raw6307step1Labels := by
      have ha : raw6307step1 = (fun i j => raw6307step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6307step1 raw6307step0; decide +kernel
      have hl : raw6307step1Labels = raw6307step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6307step0 raw6307step0Labels permutation32 permutation3
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw6308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6308Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6308step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6308step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6308step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6308step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6308 raw6308Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw6308 raw6308Labels = mixedMoment B raw6308step0 raw6308step0Labels := by
      have hz : ∀ j, raw6308 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6308step0 = (fun i j => raw6308 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6308step0 raw6308; decide +kernel
      have hl : raw6308step0Labels = raw6308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6308 raw6308Labels permutation346 hz
    mixedMoment B raw6308step0 raw6308step0Labels = mixedMoment B raw6308step1 raw6308step1Labels := by
      have ha : raw6308step1 = (fun i j => raw6308step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6308step1 raw6308step0; decide +kernel
      have hl : raw6308step1Labels = raw6308step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6308step0 raw6308step0Labels permutation139 permutation7
    mixedMoment B raw6308step1 raw6308step1Labels = mixedMoment B raw6308step2 raw6308step2Labels := by
      have ha : raw6308step2 = raw6308step1 := by apply Matrix.ext; unfold raw6308step2 raw6308step1; decide +kernel
      have hl : raw6308step1Labels = labelEmbedding1 ∘ raw6308step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6308step1 raw6308step1Labels raw6308step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw6309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6309Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6309step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6309step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6309step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6309 raw6309Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw6309 raw6309Labels = mixedMoment B raw6309step0 raw6309step0Labels := by
      have ha : raw6309step0 = (fun i j => raw6309 (permutation611 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6309step0 raw6309; decide +kernel
      have hl : raw6309step0Labels = raw6309Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6309 raw6309Labels permutation611 permutation7
    mixedMoment B raw6309step0 raw6309step0Labels = mixedMoment B raw6309step1 raw6309step1Labels := by
      have ha : raw6309step1 = raw6309step0 := by apply Matrix.ext; unfold raw6309step1 raw6309step0; decide +kernel
      have hl : raw6309step0Labels = labelEmbedding1 ∘ raw6309step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6309step0 raw6309step0Labels raw6309step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw6310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6310Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6310step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw6310step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6310step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw6310step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6310 raw6310Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw6310 raw6310Labels = mixedMoment B raw6310step0 raw6310step0Labels := by
      have hz : ∀ j, raw6310 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6310step0 = (fun i j => raw6310 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6310step0 raw6310; decide +kernel
      have hl : raw6310step0Labels = raw6310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6310 raw6310Labels permutation346 hz
    mixedMoment B raw6310step0 raw6310step0Labels = mixedMoment B raw6310step1 raw6310step1Labels := by
      have ha : raw6310step1 = (fun i j => raw6310step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6310step1 raw6310step0; decide +kernel
      have hl : raw6310step1Labels = raw6310step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6310step0 raw6310step0Labels permutation139 permutation7
    mixedMoment B raw6310step1 raw6310step1Labels = mixedMoment B raw6310step2 raw6310step2Labels := by
      have ha : raw6310step2 = raw6310step1 := by apply Matrix.ext; unfold raw6310step2 raw6310step1; decide +kernel
      have hl : raw6310step1Labels = labelEmbedding1 ∘ raw6310step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6310step1 raw6310step1Labels raw6310step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw6311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6311Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6311step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw6311step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw6311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6311 raw6311Labels = mixedMoment B node3858 node3858Labels := by
  calc
    mixedMoment B raw6311 raw6311Labels = mixedMoment B raw6311step0 raw6311step0Labels := by
      have hz : ∀ j, raw6311 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6311step0 = (fun i j => raw6311 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6311step0 raw6311; decide +kernel
      have hl : raw6311step0Labels = raw6311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6311 raw6311Labels permutation346 hz
    mixedMoment B raw6311step0 raw6311step0Labels = mixedMoment B raw6311step1 raw6311step1Labels := by
      have ha : raw6311step1 = (fun i j => raw6311step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6311step1 raw6311step0; decide +kernel
      have hl : raw6311step1Labels = raw6311step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6311step0 raw6311step0Labels permutation137 permutation7
    mixedMoment B raw6311step1 raw6311step1Labels = mixedMoment B raw6311step2 raw6311step2Labels := by
      have ha : raw6311step2 = raw6311step1 := by apply Matrix.ext; unfold raw6311step2 raw6311step1; decide +kernel
      have hl : raw6311step1Labels = labelEmbedding1 ∘ raw6311step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6311step1 raw6311step1Labels raw6311step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3858 node3858Labels := by rfl

def raw6312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6312Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6312step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6312step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6312step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6312 raw6312Labels = mixedMoment B node3997 node3997Labels := by
  calc
    mixedMoment B raw6312 raw6312Labels = mixedMoment B raw6312step0 raw6312step0Labels := by
      have hz : ∀ j, raw6312 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6312step0 = (fun i j => raw6312 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6312step0 raw6312; decide +kernel
      have hl : raw6312step0Labels = raw6312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6312 raw6312Labels permutation346 hz
    mixedMoment B raw6312step0 raw6312step0Labels = mixedMoment B raw6312step1 raw6312step1Labels := by
      have ha : raw6312step1 = (fun i j => raw6312step0 (permutation121 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6312step1 raw6312step0; decide +kernel
      have hl : raw6312step1Labels = raw6312step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6312step0 raw6312step0Labels permutation121 permutation5
    mixedMoment B raw6312step1 raw6312step1Labels = mixedMoment B raw6312step2 raw6312step2Labels := by
      have ha : raw6312step2 = raw6312step1 := by apply Matrix.ext; unfold raw6312step2 raw6312step1; decide +kernel
      have hl : raw6312step1Labels = labelEmbedding1 ∘ raw6312step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6312step1 raw6312step1Labels raw6312step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3997 node3997Labels := by rfl

def raw6313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6313Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6313step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6313step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6313step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6313step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6313step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6313 raw6313Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw6313 raw6313Labels = mixedMoment B raw6313step0 raw6313step0Labels := by
      have hz : ∀ j, raw6313 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6313step0 = (fun i j => raw6313 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6313step0 raw6313; decide +kernel
      have hl : raw6313step0Labels = raw6313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6313 raw6313Labels permutation346 hz
    mixedMoment B raw6313step0 raw6313step0Labels = mixedMoment B raw6313step1 raw6313step1Labels := by
      have ha : raw6313step1 = (fun i j => raw6313step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6313step1 raw6313step0; decide +kernel
      have hl : raw6313step1Labels = raw6313step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6313step0 raw6313step0Labels permutation36 permutation5
    mixedMoment B raw6313step1 raw6313step1Labels = mixedMoment B raw6313step2 raw6313step2Labels := by
      have ha : raw6313step2 = -raw6313step1 := by apply Matrix.ext; change ∀ i j, raw6313step2 i j = -(raw6313step1 i j); unfold raw6313step2 raw6313step1; decide +kernel
      have hl : raw6313step2Labels = raw6313step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6313step2 raw6313step2Labels = mixedMoment B raw6313step3 raw6313step3Labels := by
      have ha : raw6313step3 = raw6313step2 := by apply Matrix.ext; unfold raw6313step3 raw6313step2; decide +kernel
      have hl : raw6313step2Labels = labelEmbedding1 ∘ raw6313step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6313step2 raw6313step2Labels raw6313step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

def raw6314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6314Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6314step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6314step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6314step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6314step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6314step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6314 raw6314Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw6314 raw6314Labels = mixedMoment B raw6314step0 raw6314step0Labels := by
      have ha : raw6314step0 = (fun i j => raw6314 (permutation180 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6314step0 raw6314; decide +kernel
      have hl : raw6314step0Labels = raw6314Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6314 raw6314Labels permutation180 permutation5
    mixedMoment B raw6314step0 raw6314step0Labels = mixedMoment B raw6314step1 raw6314step1Labels := by
      have ha : raw6314step1 = -raw6314step0 := by apply Matrix.ext; change ∀ i j, raw6314step1 i j = -(raw6314step0 i j); unfold raw6314step1 raw6314step0; decide +kernel
      have hl : raw6314step1Labels = raw6314step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6314step1 raw6314step1Labels = mixedMoment B raw6314step2 raw6314step2Labels := by
      have ha : raw6314step2 = raw6314step1 := by apply Matrix.ext; unfold raw6314step2 raw6314step1; decide +kernel
      have hl : raw6314step1Labels = labelEmbedding1 ∘ raw6314step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6314step1 raw6314step1Labels raw6314step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3463 node3463Labels := by rfl

def raw6315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6315Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6315step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw6315step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6315step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw6315step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6315step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw6315step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6315 raw6315Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw6315 raw6315Labels = mixedMoment B raw6315step0 raw6315step0Labels := by
      have hz : ∀ j, raw6315 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6315step0 = (fun i j => raw6315 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6315step0 raw6315; decide +kernel
      have hl : raw6315step0Labels = raw6315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6315 raw6315Labels permutation346 hz
    mixedMoment B raw6315step0 raw6315step0Labels = mixedMoment B raw6315step1 raw6315step1Labels := by
      have ha : raw6315step1 = (fun i j => raw6315step0 (permutation39 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6315step1 raw6315step0; decide +kernel
      have hl : raw6315step1Labels = raw6315step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6315step0 raw6315step0Labels permutation39 permutation5
    mixedMoment B raw6315step1 raw6315step1Labels = mixedMoment B raw6315step2 raw6315step2Labels := by
      have ha : raw6315step2 = -raw6315step1 := by apply Matrix.ext; change ∀ i j, raw6315step2 i j = -(raw6315step1 i j); unfold raw6315step2 raw6315step1; decide +kernel
      have hl : raw6315step2Labels = raw6315step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6315step2 raw6315step2Labels = mixedMoment B raw6315step3 raw6315step3Labels := by
      have ha : raw6315step3 = raw6315step2 := by apply Matrix.ext; unfold raw6315step3 raw6315step2; decide +kernel
      have hl : raw6315step2Labels = labelEmbedding1 ∘ raw6315step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6315step2 raw6315step2Labels raw6315step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

def raw6316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6316Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6316step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw6316step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6316step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw6316step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6316step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw6316step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6316 raw6316Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw6316 raw6316Labels = mixedMoment B raw6316step0 raw6316step0Labels := by
      have hz : ∀ j, raw6316 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6316step0 = (fun i j => raw6316 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6316step0 raw6316; decide +kernel
      have hl : raw6316step0Labels = raw6316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6316 raw6316Labels permutation346 hz
    mixedMoment B raw6316step0 raw6316step0Labels = mixedMoment B raw6316step1 raw6316step1Labels := by
      have ha : raw6316step1 = (fun i j => raw6316step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6316step1 raw6316step0; decide +kernel
      have hl : raw6316step1Labels = raw6316step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6316step0 raw6316step0Labels permutation36 permutation5
    mixedMoment B raw6316step1 raw6316step1Labels = mixedMoment B raw6316step2 raw6316step2Labels := by
      have ha : raw6316step2 = -raw6316step1 := by apply Matrix.ext; change ∀ i j, raw6316step2 i j = -(raw6316step1 i j); unfold raw6316step2 raw6316step1; decide +kernel
      have hl : raw6316step2Labels = raw6316step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6316step2 raw6316step2Labels = mixedMoment B raw6316step3 raw6316step3Labels := by
      have ha : raw6316step3 = raw6316step2 := by apply Matrix.ext; unfold raw6316step3 raw6316step2; decide +kernel
      have hl : raw6316step2Labels = labelEmbedding1 ∘ raw6316step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6316step2 raw6316step2Labels raw6316step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3625 node3625Labels := by rfl

def raw6317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6317Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6317step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw6317step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6317step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6317step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6317step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6317 raw6317Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw6317 raw6317Labels = mixedMoment B raw6317step0 raw6317step0Labels := by
      have hz : ∀ j, raw6317 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6317step0 = (fun i j => raw6317 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6317step0 raw6317; decide +kernel
      have hl : raw6317step0Labels = raw6317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6317 raw6317Labels permutation346 hz
    mixedMoment B raw6317step0 raw6317step0Labels = mixedMoment B raw6317step1 raw6317step1Labels := by
      have ha : raw6317step1 = (fun i j => raw6317step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6317step1 raw6317step0; decide +kernel
      have hl : raw6317step1Labels = raw6317step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6317step0 raw6317step0Labels permutation50 permutation5
    mixedMoment B raw6317step1 raw6317step1Labels = mixedMoment B raw6317step2 raw6317step2Labels := by
      have ha : raw6317step2 = -raw6317step1 := by apply Matrix.ext; change ∀ i j, raw6317step2 i j = -(raw6317step1 i j); unfold raw6317step2 raw6317step1; decide +kernel
      have hl : raw6317step2Labels = raw6317step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6317step2 raw6317step2Labels = mixedMoment B raw6317step3 raw6317step3Labels := by
      have ha : raw6317step3 = raw6317step2 := by apply Matrix.ext; unfold raw6317step3 raw6317step2; decide +kernel
      have hl : raw6317step2Labels = labelEmbedding1 ∘ raw6317step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6317step2 raw6317step2Labels raw6317step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw6318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6318Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw6318step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6318step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6318step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6318step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6318 raw6318Labels = mixedMoment B node1607 node1607Labels := by
  calc
    mixedMoment B raw6318 raw6318Labels = mixedMoment B raw6318step0 raw6318step0Labels := by
      have ha : raw6318step0 = (fun i j => raw6318 (permutation172 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6318step0 raw6318; decide +kernel
      have hl : raw6318step0Labels = raw6318Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6318 raw6318Labels permutation172 permutation5
    mixedMoment B raw6318step0 raw6318step0Labels = mixedMoment B raw6318step1 raw6318step1Labels := by
      have ha : raw6318step1 = -raw6318step0 := by apply Matrix.ext; change ∀ i j, raw6318step1 i j = -(raw6318step0 i j); unfold raw6318step1 raw6318step0; decide +kernel
      have hl : raw6318step1Labels = raw6318step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6318step1 raw6318step1Labels = mixedMoment B raw6318step2 raw6318step2Labels := by
      have ha : raw6318step2 = raw6318step1 := by apply Matrix.ext; unfold raw6318step2 raw6318step1; decide +kernel
      have hl : raw6318step1Labels = labelEmbedding1 ∘ raw6318step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6318step1 raw6318step1Labels raw6318step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1607 node1607Labels := by rfl

def raw6319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6319Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw6319step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6319step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6319step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6319step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6319step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6319 raw6319Labels = mixedMoment B node3346 node3346Labels := by
  calc
    mixedMoment B raw6319 raw6319Labels = mixedMoment B raw6319step0 raw6319step0Labels := by
      have ha : raw6319step0 = (fun i j => raw6319 (permutation172 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6319step0 raw6319; decide +kernel
      have hl : raw6319step0Labels = raw6319Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6319 raw6319Labels permutation172 permutation5
    mixedMoment B raw6319step0 raw6319step0Labels = mixedMoment B raw6319step1 raw6319step1Labels := by
      have ha : raw6319step1 = -raw6319step0 := by apply Matrix.ext; change ∀ i j, raw6319step1 i j = -(raw6319step0 i j); unfold raw6319step1 raw6319step0; decide +kernel
      have hl : raw6319step1Labels = raw6319step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6319step1 raw6319step1Labels = mixedMoment B raw6319step2 raw6319step2Labels := by
      have ha : raw6319step2 = raw6319step1 := by apply Matrix.ext; unfold raw6319step2 raw6319step1; decide +kernel
      have hl : raw6319step1Labels = labelEmbedding1 ∘ raw6319step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6319step1 raw6319step1Labels raw6319step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3346 node3346Labels := by rfl

def raw6320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6320Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw6320step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6320step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6320step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6320step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6320 raw6320Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw6320 raw6320Labels = mixedMoment B raw6320step0 raw6320step0Labels := by
      have ha : raw6320step0 = (fun i j => raw6320 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6320step0 raw6320; decide +kernel
      have hl : raw6320step0Labels = raw6320Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6320 raw6320Labels permutation162 permutation5
    mixedMoment B raw6320step0 raw6320step0Labels = mixedMoment B raw6320step1 raw6320step1Labels := by
      have ha : raw6320step1 = -raw6320step0 := by apply Matrix.ext; change ∀ i j, raw6320step1 i j = -(raw6320step0 i j); unfold raw6320step1 raw6320step0; decide +kernel
      have hl : raw6320step1Labels = raw6320step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6320step1 raw6320step1Labels = mixedMoment B raw6320step2 raw6320step2Labels := by
      have ha : raw6320step2 = raw6320step1 := by apply Matrix.ext; unfold raw6320step2 raw6320step1; decide +kernel
      have hl : raw6320step1Labels = labelEmbedding1 ∘ raw6320step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6320step1 raw6320step1Labels raw6320step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

def raw6321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6321Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw6321step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6321step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw6321step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6321step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw6321step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6321 raw6321Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw6321 raw6321Labels = mixedMoment B raw6321step0 raw6321step0Labels := by
      have ha : raw6321step0 = (fun i j => raw6321 (permutation173 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6321step0 raw6321; decide +kernel
      have hl : raw6321step0Labels = raw6321Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6321 raw6321Labels permutation173 permutation5
    mixedMoment B raw6321step0 raw6321step0Labels = mixedMoment B raw6321step1 raw6321step1Labels := by
      have ha : raw6321step1 = -raw6321step0 := by apply Matrix.ext; change ∀ i j, raw6321step1 i j = -(raw6321step0 i j); unfold raw6321step1 raw6321step0; decide +kernel
      have hl : raw6321step1Labels = raw6321step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6321step1 raw6321step1Labels = mixedMoment B raw6321step2 raw6321step2Labels := by
      have ha : raw6321step2 = raw6321step1 := by apply Matrix.ext; unfold raw6321step2 raw6321step1; decide +kernel
      have hl : raw6321step1Labels = labelEmbedding1 ∘ raw6321step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6321step1 raw6321step1Labels raw6321step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

def raw6322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6322Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw6322step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6322step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6322step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6322step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6322 raw6322Labels = mixedMoment B node3503 node3503Labels := by
  calc
    mixedMoment B raw6322 raw6322Labels = mixedMoment B raw6322step0 raw6322step0Labels := by
      have ha : raw6322step0 = (fun i j => raw6322 (permutation172 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6322step0 raw6322; decide +kernel
      have hl : raw6322step0Labels = raw6322Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6322 raw6322Labels permutation172 permutation5
    mixedMoment B raw6322step0 raw6322step0Labels = mixedMoment B raw6322step1 raw6322step1Labels := by
      have ha : raw6322step1 = -raw6322step0 := by apply Matrix.ext; change ∀ i j, raw6322step1 i j = -(raw6322step0 i j); unfold raw6322step1 raw6322step0; decide +kernel
      have hl : raw6322step1Labels = raw6322step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6322step1 raw6322step1Labels = mixedMoment B raw6322step2 raw6322step2Labels := by
      have ha : raw6322step2 = raw6322step1 := by apply Matrix.ext; unfold raw6322step2 raw6322step1; decide +kernel
      have hl : raw6322step1Labels = labelEmbedding1 ∘ raw6322step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6322step1 raw6322step1Labels raw6322step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3503 node3503Labels := by rfl

def raw6323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6323Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6323step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6323step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw6323step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6323step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6323step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6323step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6323step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6323 raw6323Labels = mixedMoment B node1612 node1612Labels := by
  calc
    mixedMoment B raw6323 raw6323Labels = mixedMoment B raw6323step0 raw6323step0Labels := by
      have hz : ∀ j, raw6323 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6323step0 = (fun i j => raw6323 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6323step0 raw6323; decide +kernel
      have hl : raw6323step0Labels = raw6323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6323 raw6323Labels permutation346 hz
    mixedMoment B raw6323step0 raw6323step0Labels = mixedMoment B raw6323step1 raw6323step1Labels := by
      have ha : raw6323step1 = (fun i j => raw6323step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6323step1 raw6323step0; decide +kernel
      have hl : raw6323step1Labels = raw6323step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6323step0 raw6323step0Labels permutation36 permutation5
    mixedMoment B raw6323step1 raw6323step1Labels = mixedMoment B raw6323step2 raw6323step2Labels := by
      have ha : raw6323step2 = -raw6323step1 := by apply Matrix.ext; change ∀ i j, raw6323step2 i j = -(raw6323step1 i j); unfold raw6323step2 raw6323step1; decide +kernel
      have hl : raw6323step2Labels = raw6323step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6323step2 raw6323step2Labels = mixedMoment B raw6323step3 raw6323step3Labels := by
      have ha : raw6323step3 = raw6323step2 := by apply Matrix.ext; unfold raw6323step3 raw6323step2; decide +kernel
      have hl : raw6323step2Labels = labelEmbedding1 ∘ raw6323step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6323step2 raw6323step2Labels raw6323step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1612 node1612Labels := by rfl

def raw6324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6324Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6324step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw6324step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6324step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6324step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6324step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6324 raw6324Labels = mixedMoment B node3349 node3349Labels := by
  calc
    mixedMoment B raw6324 raw6324Labels = mixedMoment B raw6324step0 raw6324step0Labels := by
      have hz : ∀ j, raw6324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6324step0 = (fun i j => raw6324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6324step0 raw6324; decide +kernel
      have hl : raw6324step0Labels = raw6324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6324 raw6324Labels permutation346 hz
    mixedMoment B raw6324step0 raw6324step0Labels = mixedMoment B raw6324step1 raw6324step1Labels := by
      have ha : raw6324step1 = (fun i j => raw6324step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6324step1 raw6324step0; decide +kernel
      have hl : raw6324step1Labels = raw6324step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6324step0 raw6324step0Labels permutation36 permutation5
    mixedMoment B raw6324step1 raw6324step1Labels = mixedMoment B raw6324step2 raw6324step2Labels := by
      have ha : raw6324step2 = -raw6324step1 := by apply Matrix.ext; change ∀ i j, raw6324step2 i j = -(raw6324step1 i j); unfold raw6324step2 raw6324step1; decide +kernel
      have hl : raw6324step2Labels = raw6324step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6324step2 raw6324step2Labels = mixedMoment B raw6324step3 raw6324step3Labels := by
      have ha : raw6324step3 = raw6324step2 := by apply Matrix.ext; unfold raw6324step3 raw6324step2; decide +kernel
      have hl : raw6324step2Labels = labelEmbedding1 ∘ raw6324step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6324step2 raw6324step2Labels raw6324step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3349 node3349Labels := by rfl

def raw6325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6325Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw6325step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6325step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6325step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6325step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6325step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6325 raw6325Labels = mixedMoment B node3431 node3431Labels := by
  calc
    mixedMoment B raw6325 raw6325Labels = mixedMoment B raw6325step0 raw6325step0Labels := by
      have ha : raw6325step0 = (fun i j => raw6325 (permutation180 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6325step0 raw6325; decide +kernel
      have hl : raw6325step0Labels = raw6325Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6325 raw6325Labels permutation180 permutation5
    mixedMoment B raw6325step0 raw6325step0Labels = mixedMoment B raw6325step1 raw6325step1Labels := by
      have ha : raw6325step1 = -raw6325step0 := by apply Matrix.ext; change ∀ i j, raw6325step1 i j = -(raw6325step0 i j); unfold raw6325step1 raw6325step0; decide +kernel
      have hl : raw6325step1Labels = raw6325step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6325step1 raw6325step1Labels = mixedMoment B raw6325step2 raw6325step2Labels := by
      have ha : raw6325step2 = raw6325step1 := by apply Matrix.ext; unfold raw6325step2 raw6325step1; decide +kernel
      have hl : raw6325step1Labels = labelEmbedding1 ∘ raw6325step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6325step1 raw6325step1Labels raw6325step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3431 node3431Labels := by rfl

def raw6326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6326Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6326step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw6326step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6326step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6326step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6326step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6326 raw6326Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw6326 raw6326Labels = mixedMoment B raw6326step0 raw6326step0Labels := by
      have hz : ∀ j, raw6326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6326step0 = (fun i j => raw6326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6326step0 raw6326; decide +kernel
      have hl : raw6326step0Labels = raw6326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6326 raw6326Labels permutation346 hz
    mixedMoment B raw6326step0 raw6326step0Labels = mixedMoment B raw6326step1 raw6326step1Labels := by
      have ha : raw6326step1 = (fun i j => raw6326step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6326step1 raw6326step0; decide +kernel
      have hl : raw6326step1Labels = raw6326step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6326step0 raw6326step0Labels permutation37 permutation5
    mixedMoment B raw6326step1 raw6326step1Labels = mixedMoment B raw6326step2 raw6326step2Labels := by
      have ha : raw6326step2 = -raw6326step1 := by apply Matrix.ext; change ∀ i j, raw6326step2 i j = -(raw6326step1 i j); unfold raw6326step2 raw6326step1; decide +kernel
      have hl : raw6326step2Labels = raw6326step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6326step2 raw6326step2Labels = mixedMoment B raw6326step3 raw6326step3Labels := by
      have ha : raw6326step3 = raw6326step2 := by apply Matrix.ext; unfold raw6326step3 raw6326step2; decide +kernel
      have hl : raw6326step2Labels = labelEmbedding1 ∘ raw6326step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6326step2 raw6326step2Labels raw6326step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw6327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6327Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6327step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw6327step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw6327step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6327step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw6327step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6327 raw6327Labels = mixedMoment B node3507 node3507Labels := by
  calc
    mixedMoment B raw6327 raw6327Labels = mixedMoment B raw6327step0 raw6327step0Labels := by
      have hz : ∀ j, raw6327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6327step0 = (fun i j => raw6327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6327step0 raw6327; decide +kernel
      have hl : raw6327step0Labels = raw6327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6327 raw6327Labels permutation346 hz
    mixedMoment B raw6327step0 raw6327step0Labels = mixedMoment B raw6327step1 raw6327step1Labels := by
      have ha : raw6327step1 = (fun i j => raw6327step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6327step1 raw6327step0; decide +kernel
      have hl : raw6327step1Labels = raw6327step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6327step0 raw6327step0Labels permutation36 permutation5
    mixedMoment B raw6327step1 raw6327step1Labels = mixedMoment B raw6327step2 raw6327step2Labels := by
      have ha : raw6327step2 = -raw6327step1 := by apply Matrix.ext; change ∀ i j, raw6327step2 i j = -(raw6327step1 i j); unfold raw6327step2 raw6327step1; decide +kernel
      have hl : raw6327step2Labels = raw6327step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6327step2 raw6327step2Labels = mixedMoment B raw6327step3 raw6327step3Labels := by
      have ha : raw6327step3 = raw6327step2 := by apply Matrix.ext; unfold raw6327step3 raw6327step2; decide +kernel
      have hl : raw6327step2Labels = labelEmbedding1 ∘ raw6327step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6327step2 raw6327step2Labels raw6327step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3507 node3507Labels := by rfl

def raw6328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6328Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6328step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw6328step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6328step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw6328step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6328step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw6328step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6328 raw6328Labels = mixedMoment B node1608 node1608Labels := by
  calc
    mixedMoment B raw6328 raw6328Labels = mixedMoment B raw6328step0 raw6328step0Labels := by
      have hz : ∀ j, raw6328 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6328step0 = (fun i j => raw6328 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6328step0 raw6328; decide +kernel
      have hl : raw6328step0Labels = raw6328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6328 raw6328Labels permutation346 hz
    mixedMoment B raw6328step0 raw6328step0Labels = mixedMoment B raw6328step1 raw6328step1Labels := by
      have ha : raw6328step1 = (fun i j => raw6328step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6328step1 raw6328step0; decide +kernel
      have hl : raw6328step1Labels = raw6328step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6328step0 raw6328step0Labels permutation36 permutation5
    mixedMoment B raw6328step1 raw6328step1Labels = mixedMoment B raw6328step2 raw6328step2Labels := by
      have ha : raw6328step2 = -raw6328step1 := by apply Matrix.ext; change ∀ i j, raw6328step2 i j = -(raw6328step1 i j); unfold raw6328step2 raw6328step1; decide +kernel
      have hl : raw6328step2Labels = raw6328step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6328step2 raw6328step2Labels = mixedMoment B raw6328step3 raw6328step3Labels := by
      have ha : raw6328step3 = raw6328step2 := by apply Matrix.ext; unfold raw6328step3 raw6328step2; decide +kernel
      have hl : raw6328step2Labels = labelEmbedding1 ∘ raw6328step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6328step2 raw6328step2Labels raw6328step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1608 node1608Labels := by rfl

def raw6329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6329Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6329step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw6329step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw6329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6329 raw6329Labels = mixedMoment B node2538 node2538Labels := by
  calc
    mixedMoment B raw6329 raw6329Labels = mixedMoment B raw6329step0 raw6329step0Labels := by
      have hz : ∀ j, raw6329 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6329step0 = (fun i j => raw6329 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6329step0 raw6329; decide +kernel
      have hl : raw6329step0Labels = raw6329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6329 raw6329Labels permutation346 hz
    mixedMoment B raw6329step0 raw6329step0Labels = mixedMoment B raw6329step1 raw6329step1Labels := by
      have ha : raw6329step1 = (fun i j => raw6329step0 (permutation121 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6329step1 raw6329step0; decide +kernel
      have hl : raw6329step1Labels = raw6329step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6329step0 raw6329step0Labels permutation121 permutation5
    mixedMoment B raw6329step1 raw6329step1Labels = mixedMoment B raw6329step2 raw6329step2Labels := by
      have ha : raw6329step2 = raw6329step1 := by apply Matrix.ext; unfold raw6329step2 raw6329step1; decide +kernel
      have hl : raw6329step1Labels = labelEmbedding1 ∘ raw6329step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6329step1 raw6329step1Labels raw6329step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2538 node2538Labels := by rfl

def raw6330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6330Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6330step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw6330step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6330step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw6330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6330 raw6330Labels = mixedMoment B node2534 node2534Labels := by
  calc
    mixedMoment B raw6330 raw6330Labels = mixedMoment B raw6330step0 raw6330step0Labels := by
      have ha : raw6330step0 = (fun i j => raw6330 (permutation566 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6330step0 raw6330; decide +kernel
      have hl : raw6330step0Labels = raw6330Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6330 raw6330Labels permutation566 permutation5
    mixedMoment B raw6330step0 raw6330step0Labels = mixedMoment B raw6330step1 raw6330step1Labels := by
      have ha : raw6330step1 = raw6330step0 := by apply Matrix.ext; unfold raw6330step1 raw6330step0; decide +kernel
      have hl : raw6330step0Labels = labelEmbedding1 ∘ raw6330step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6330step0 raw6330step0Labels raw6330step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2534 node2534Labels := by rfl

def raw6331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6331Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6331step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw6331step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw6331step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6331 raw6331Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw6331 raw6331Labels = mixedMoment B raw6331step0 raw6331step0Labels := by
      have hz : ∀ j, raw6331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6331step0 = (fun i j => raw6331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6331step0 raw6331; decide +kernel
      have hl : raw6331step0Labels = raw6331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6331 raw6331Labels permutation346 hz
    mixedMoment B raw6331step0 raw6331step0Labels = mixedMoment B raw6331step1 raw6331step1Labels := by
      have ha : raw6331step1 = (fun i j => raw6331step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6331step1 raw6331step0; decide +kernel
      have hl : raw6331step1Labels = raw6331step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6331step0 raw6331step0Labels permutation127 permutation5
    mixedMoment B raw6331step1 raw6331step1Labels = mixedMoment B raw6331step2 raw6331step2Labels := by
      have ha : raw6331step2 = raw6331step1 := by apply Matrix.ext; unfold raw6331step2 raw6331step1; decide +kernel
      have hl : raw6331step1Labels = labelEmbedding1 ∘ raw6331step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6331step1 raw6331step1Labels raw6331step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2670 node2670Labels := by rfl

def raw6332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![1, 1, -2]]
def raw6332Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![1, 1, -2]]
def raw6332step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw6332step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6332step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw6332step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6332 raw6332Labels = mixedMoment B node2588 node2588Labels := by
  calc
    mixedMoment B raw6332 raw6332Labels = mixedMoment B raw6332step0 raw6332step0Labels := by
      have hz : ∀ j, raw6332 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6332step0 = (fun i j => raw6332 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6332step0 raw6332; decide +kernel
      have hl : raw6332step0Labels = raw6332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6332 raw6332Labels permutation346 hz
    mixedMoment B raw6332step0 raw6332step0Labels = mixedMoment B raw6332step1 raw6332step1Labels := by
      have ha : raw6332step1 = (fun i j => raw6332step0 (permutation121 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6332step1 raw6332step0; decide +kernel
      have hl : raw6332step1Labels = raw6332step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6332step0 raw6332step0Labels permutation121 permutation5
    mixedMoment B raw6332step1 raw6332step1Labels = mixedMoment B raw6332step2 raw6332step2Labels := by
      have ha : raw6332step2 = raw6332step1 := by apply Matrix.ext; unfold raw6332step2 raw6332step1; decide +kernel
      have hl : raw6332step1Labels = labelEmbedding1 ∘ raw6332step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6332step1 raw6332step1Labels raw6332step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2588 node2588Labels := by rfl

def raw6333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6333Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6333step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw6333step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6333step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6333step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6333step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6333step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6333 raw6333Labels = mixedMoment B node1619 node1619Labels := by
  calc
    mixedMoment B raw6333 raw6333Labels = mixedMoment B raw6333step0 raw6333step0Labels := by
      have hz : ∀ j, raw6333 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6333step0 = (fun i j => raw6333 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6333step0 raw6333; decide +kernel
      have hl : raw6333step0Labels = raw6333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6333 raw6333Labels permutation346 hz
    mixedMoment B raw6333step0 raw6333step0Labels = mixedMoment B raw6333step1 raw6333step1Labels := by
      have ha : raw6333step1 = (fun i j => raw6333step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6333step1 raw6333step0; decide +kernel
      have hl : raw6333step1Labels = raw6333step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6333step0 raw6333step0Labels permutation33 permutation5
    mixedMoment B raw6333step1 raw6333step1Labels = mixedMoment B raw6333step2 raw6333step2Labels := by
      have ha : raw6333step2 = -raw6333step1 := by apply Matrix.ext; change ∀ i j, raw6333step2 i j = -(raw6333step1 i j); unfold raw6333step2 raw6333step1; decide +kernel
      have hl : raw6333step2Labels = raw6333step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6333step2 raw6333step2Labels = mixedMoment B raw6333step3 raw6333step3Labels := by
      have ha : raw6333step3 = raw6333step2 := by apply Matrix.ext; unfold raw6333step3 raw6333step2; decide +kernel
      have hl : raw6333step2Labels = labelEmbedding1 ∘ raw6333step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6333step2 raw6333step2Labels raw6333step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1619 node1619Labels := by rfl

def raw6334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6334Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6334step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6334step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw6334step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6334step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6334step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6334step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6334step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6334 raw6334Labels = mixedMoment B node3355 node3355Labels := by
  calc
    mixedMoment B raw6334 raw6334Labels = mixedMoment B raw6334step0 raw6334step0Labels := by
      have hz : ∀ j, raw6334 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6334step0 = (fun i j => raw6334 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6334step0 raw6334; decide +kernel
      have hl : raw6334step0Labels = raw6334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6334 raw6334Labels permutation346 hz
    mixedMoment B raw6334step0 raw6334step0Labels = mixedMoment B raw6334step1 raw6334step1Labels := by
      have ha : raw6334step1 = (fun i j => raw6334step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6334step1 raw6334step0; decide +kernel
      have hl : raw6334step1Labels = raw6334step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6334step0 raw6334step0Labels permutation33 permutation5
    mixedMoment B raw6334step1 raw6334step1Labels = mixedMoment B raw6334step2 raw6334step2Labels := by
      have ha : raw6334step2 = -raw6334step1 := by apply Matrix.ext; change ∀ i j, raw6334step2 i j = -(raw6334step1 i j); unfold raw6334step2 raw6334step1; decide +kernel
      have hl : raw6334step2Labels = raw6334step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6334step2 raw6334step2Labels = mixedMoment B raw6334step3 raw6334step3Labels := by
      have ha : raw6334step3 = raw6334step2 := by apply Matrix.ext; unfold raw6334step3 raw6334step2; decide +kernel
      have hl : raw6334step2Labels = labelEmbedding1 ∘ raw6334step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6334step2 raw6334step2Labels raw6334step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3355 node3355Labels := by rfl

def raw6335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6335Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw6335step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6335step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6335step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6335step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6335step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6335 raw6335Labels = mixedMoment B node3434 node3434Labels := by
  calc
    mixedMoment B raw6335 raw6335Labels = mixedMoment B raw6335step0 raw6335step0Labels := by
      have ha : raw6335step0 = (fun i j => raw6335 (permutation177 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6335step0 raw6335; decide +kernel
      have hl : raw6335step0Labels = raw6335Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6335 raw6335Labels permutation177 permutation5
    mixedMoment B raw6335step0 raw6335step0Labels = mixedMoment B raw6335step1 raw6335step1Labels := by
      have ha : raw6335step1 = -raw6335step0 := by apply Matrix.ext; change ∀ i j, raw6335step1 i j = -(raw6335step0 i j); unfold raw6335step1 raw6335step0; decide +kernel
      have hl : raw6335step1Labels = raw6335step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6335step1 raw6335step1Labels = mixedMoment B raw6335step2 raw6335step2Labels := by
      have ha : raw6335step2 = raw6335step1 := by apply Matrix.ext; unfold raw6335step2 raw6335step1; decide +kernel
      have hl : raw6335step1Labels = labelEmbedding1 ∘ raw6335step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6335step1 raw6335step1Labels raw6335step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3434 node3434Labels := by rfl

def raw6336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6336Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6336step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw6336step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6336step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw6336step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6336step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw6336step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6336 raw6336Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw6336 raw6336Labels = mixedMoment B raw6336step0 raw6336step0Labels := by
      have hz : ∀ j, raw6336 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6336step0 = (fun i j => raw6336 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6336step0 raw6336; decide +kernel
      have hl : raw6336step0Labels = raw6336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6336 raw6336Labels permutation346 hz
    mixedMoment B raw6336step0 raw6336step0Labels = mixedMoment B raw6336step1 raw6336step1Labels := by
      have ha : raw6336step1 = (fun i j => raw6336step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6336step1 raw6336step0; decide +kernel
      have hl : raw6336step1Labels = raw6336step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6336step0 raw6336step0Labels permutation33 permutation5
    mixedMoment B raw6336step1 raw6336step1Labels = mixedMoment B raw6336step2 raw6336step2Labels := by
      have ha : raw6336step2 = -raw6336step1 := by apply Matrix.ext; change ∀ i j, raw6336step2 i j = -(raw6336step1 i j); unfold raw6336step2 raw6336step1; decide +kernel
      have hl : raw6336step2Labels = raw6336step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6336step2 raw6336step2Labels = mixedMoment B raw6336step3 raw6336step3Labels := by
      have ha : raw6336step3 = raw6336step2 := by apply Matrix.ext; unfold raw6336step3 raw6336step2; decide +kernel
      have hl : raw6336step2Labels = labelEmbedding1 ∘ raw6336step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6336step2 raw6336step2Labels raw6336step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

def raw6337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw6337Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw6337step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6337step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw6337step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6337step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw6337step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6337step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw6337step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6337 raw6337Labels = mixedMoment B node3543 node3543Labels := by
  calc
    mixedMoment B raw6337 raw6337Labels = mixedMoment B raw6337step0 raw6337step0Labels := by
      have hz : ∀ j, raw6337 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6337step0 = (fun i j => raw6337 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6337step0 raw6337; decide +kernel
      have hl : raw6337step0Labels = raw6337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6337 raw6337Labels permutation346 hz
    mixedMoment B raw6337step0 raw6337step0Labels = mixedMoment B raw6337step1 raw6337step1Labels := by
      have ha : raw6337step1 = (fun i j => raw6337step0 (permutation32 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6337step1 raw6337step0; decide +kernel
      have hl : raw6337step1Labels = raw6337step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6337step0 raw6337step0Labels permutation32 permutation5
    mixedMoment B raw6337step1 raw6337step1Labels = mixedMoment B raw6337step2 raw6337step2Labels := by
      have ha : raw6337step2 = -raw6337step1 := by apply Matrix.ext; change ∀ i j, raw6337step2 i j = -(raw6337step1 i j); unfold raw6337step2 raw6337step1; decide +kernel
      have hl : raw6337step2Labels = raw6337step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6337step2 raw6337step2Labels = mixedMoment B raw6337step3 raw6337step3Labels := by
      have ha : raw6337step3 = raw6337step2 := by apply Matrix.ext; unfold raw6337step3 raw6337step2; decide +kernel
      have hl : raw6337step2Labels = labelEmbedding1 ∘ raw6337step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6337step2 raw6337step2Labels raw6337step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3543 node3543Labels := by rfl

def raw6338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6338 raw6338Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw6338 raw6338Labels = mixedMoment B raw6338step0 raw6338step0Labels := by
      have hz : ∀ j, raw6338 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6338step0 = (fun i j => raw6338 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6338step0 raw6338; decide +kernel
      have hl : raw6338step0Labels = raw6338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6338 raw6338Labels permutation346 hz
    mixedMoment B raw6338step0 raw6338step0Labels = mixedMoment B raw6338step1 raw6338step1Labels := by
      have ha : raw6338step1 = (fun i j => raw6338step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6338step1 raw6338step0; decide +kernel
      have hl : raw6338step1Labels = raw6338step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6338step0 raw6338step0Labels permutation38 permutation2
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw6339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw6339step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6339step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw6339step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6339 raw6339Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw6339 raw6339Labels = mixedMoment B raw6339step0 raw6339step0Labels := by
      have hz : ∀ j, raw6339 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6339step0 = (fun i j => raw6339 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6339step0 raw6339; decide +kernel
      have hl : raw6339step0Labels = raw6339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6339 raw6339Labels permutation346 hz
    mixedMoment B raw6339step0 raw6339step0Labels = mixedMoment B raw6339step1 raw6339step1Labels := by
      have ha : raw6339step1 = (fun i j => raw6339step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6339step1 raw6339step0; decide +kernel
      have hl : raw6339step1Labels = raw6339step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6339step0 raw6339step0Labels permutation151 permutation2
    mixedMoment B raw6339step1 raw6339step1Labels = mixedMoment B raw6339step2 raw6339step2Labels := by
      have ha : raw6339step2 = -raw6339step1 := by apply Matrix.ext; change ∀ i j, raw6339step2 i j = -(raw6339step1 i j); unfold raw6339step2 raw6339step1; decide +kernel
      have hl : raw6339step2Labels = raw6339step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw6340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6340Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw6340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6340step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw6340step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6340 raw6340Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw6340 raw6340Labels = mixedMoment B raw6340step0 raw6340step0Labels := by
      have ha : raw6340step0 = (fun i j => raw6340 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6340step0 raw6340; decide +kernel
      have hl : raw6340step0Labels = raw6340Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6340 raw6340Labels permutation676 permutation2
    mixedMoment B raw6340step0 raw6340step0Labels = mixedMoment B raw6340step1 raw6340step1Labels := by
      have ha : raw6340step1 = -raw6340step0 := by apply Matrix.ext; change ∀ i j, raw6340step1 i j = -(raw6340step0 i j); unfold raw6340step1 raw6340step0; decide +kernel
      have hl : raw6340step1Labels = raw6340step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw6341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw6341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6341step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw6341step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6341 raw6341Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw6341 raw6341Labels = mixedMoment B raw6341step0 raw6341step0Labels := by
      have hz : ∀ j, raw6341 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6341step0 = (fun i j => raw6341 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6341step0 raw6341; decide +kernel
      have hl : raw6341step0Labels = raw6341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6341 raw6341Labels permutation346 hz
    mixedMoment B raw6341step0 raw6341step0Labels = mixedMoment B raw6341step1 raw6341step1Labels := by
      have ha : raw6341step1 = (fun i j => raw6341step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6341step1 raw6341step0; decide +kernel
      have hl : raw6341step1Labels = raw6341step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6341step0 raw6341step0Labels permutation149 permutation2
    mixedMoment B raw6341step1 raw6341step1Labels = mixedMoment B raw6341step2 raw6341step2Labels := by
      have ha : raw6341step2 = -raw6341step1 := by apply Matrix.ext; change ∀ i j, raw6341step2 i j = -(raw6341step1 i j); unfold raw6341step2 raw6341step1; decide +kernel
      have hl : raw6341step2Labels = raw6341step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw6342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6342Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6342step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw6342step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6342step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw6342step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6342 raw6342Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw6342 raw6342Labels = mixedMoment B raw6342step0 raw6342step0Labels := by
      have hz : ∀ j, raw6342 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6342step0 = (fun i j => raw6342 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6342step0 raw6342; decide +kernel
      have hl : raw6342step0Labels = raw6342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6342 raw6342Labels permutation346 hz
    mixedMoment B raw6342step0 raw6342step0Labels = mixedMoment B raw6342step1 raw6342step1Labels := by
      have ha : raw6342step1 = (fun i j => raw6342step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6342step1 raw6342step0; decide +kernel
      have hl : raw6342step1Labels = raw6342step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6342step0 raw6342step0Labels permutation137 permutation2
    mixedMoment B raw6342step1 raw6342step1Labels = mixedMoment B raw6342step2 raw6342step2Labels := by
      have ha : raw6342step2 = -raw6342step1 := by apply Matrix.ext; change ∀ i j, raw6342step2 i j = -(raw6342step1 i j); unfold raw6342step2 raw6342step1; decide +kernel
      have hl : raw6342step2Labels = raw6342step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3902 node3902Labels := by rfl

def raw6343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6343Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6343step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw6343step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6343 raw6343Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw6343 raw6343Labels = mixedMoment B raw6343step0 raw6343step0Labels := by
      have hz : ∀ j, raw6343 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6343step0 = (fun i j => raw6343 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6343step0 raw6343; decide +kernel
      have hl : raw6343step0Labels = raw6343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6343 raw6343Labels permutation346 hz
    mixedMoment B raw6343step0 raw6343step0Labels = mixedMoment B raw6343step1 raw6343step1Labels := by
      have ha : raw6343step1 = (fun i j => raw6343step0 (permutation116 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6343step1 raw6343step0; decide +kernel
      have hl : raw6343step1Labels = raw6343step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6343step0 raw6343step0Labels permutation116 permutation4
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw6344 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![-1, 1], ![-1, 1], ![2, -2]]
def raw6344Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6344step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![2, -2]]
def raw6344step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6344step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw6344step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6344step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw6344step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical6344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6344 raw6344Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw6344 raw6344Labels = mixedMoment B raw6344step0 raw6344step0Labels := by
      have hz : ∀ j, raw6344 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6344step0 = (fun i j => raw6344 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6344step0 raw6344; decide +kernel
      have hl : raw6344step0Labels = raw6344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6344 raw6344Labels permutation346 hz
    mixedMoment B raw6344step0 raw6344step0Labels = mixedMoment B raw6344step1 raw6344step1Labels := by
      have ha : raw6344step1 = (fun i j => raw6344step0 (permutation134 i) (permutation0 j)) := by apply Matrix.ext; unfold raw6344step1 raw6344step0; decide +kernel
      have hl : raw6344step1Labels = raw6344step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6344step0 raw6344step0Labels permutation134 permutation0
    mixedMoment B raw6344step1 raw6344step1Labels = mixedMoment B raw6344step2 raw6344step2Labels := by
      have ha : raw6344step2 = -raw6344step1 := by apply Matrix.ext; change ∀ i j, raw6344step2 i j = -(raw6344step1 i j); unfold raw6344step2 raw6344step1; decide +kernel
      have hl : raw6344step2Labels = raw6344step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw6345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw6345step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6345 raw6345Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw6345 raw6345Labels = mixedMoment B raw6345step0 raw6345step0Labels := by
      have hz : ∀ j, raw6345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6345step0 = (fun i j => raw6345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6345step0 raw6345; decide +kernel
      have hl : raw6345step0Labels = raw6345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6345 raw6345Labels permutation346 hz
    mixedMoment B raw6345step0 raw6345step0Labels = mixedMoment B raw6345step1 raw6345step1Labels := by
      have ha : raw6345step1 = (fun i j => raw6345step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6345step1 raw6345step0; decide +kernel
      have hl : raw6345step1Labels = raw6345step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6345step0 raw6345step0Labels permutation40 permutation2
    _ = mixedMoment B node1406 node1406Labels := by rfl

def raw6346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6346Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6346 raw6346Labels = mixedMoment B node1392 node1392Labels := by
  calc
    mixedMoment B raw6346 raw6346Labels = mixedMoment B raw6346step0 raw6346step0Labels := by
      have ha : raw6346step0 = (fun i j => raw6346 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6346step0 raw6346; decide +kernel
      have hl : raw6346step0Labels = raw6346Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6346 raw6346Labels permutation202 permutation2
    _ = mixedMoment B node1392 node1392Labels := by rfl

def raw6347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6347Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6347 raw6347Labels = mixedMoment B node1425 node1425Labels := by
  calc
    mixedMoment B raw6347 raw6347Labels = mixedMoment B raw6347step0 raw6347step0Labels := by
      have hz : ∀ j, raw6347 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6347step0 = (fun i j => raw6347 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6347step0 raw6347; decide +kernel
      have hl : raw6347step0Labels = raw6347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6347 raw6347Labels permutation346 hz
    _ = mixedMoment B node1425 node1425Labels := by rfl

def raw6348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6348Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6348step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw6348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6348 raw6348Labels = mixedMoment B node1400 node1400Labels := by
  calc
    mixedMoment B raw6348 raw6348Labels = mixedMoment B raw6348step0 raw6348step0Labels := by
      have hz : ∀ j, raw6348 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6348step0 = (fun i j => raw6348 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6348step0 raw6348; decide +kernel
      have hl : raw6348step0Labels = raw6348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6348 raw6348Labels permutation346 hz
    mixedMoment B raw6348step0 raw6348step0Labels = mixedMoment B raw6348step1 raw6348step1Labels := by
      have ha : raw6348step1 = (fun i j => raw6348step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6348step1 raw6348step0; decide +kernel
      have hl : raw6348step1Labels = raw6348step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6348step0 raw6348step0Labels permutation38 permutation2
    _ = mixedMoment B node1400 node1400Labels := by rfl

def raw6349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6349Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6349step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw6349step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6349 raw6349Labels = mixedMoment B node1394 node1394Labels := by
  calc
    mixedMoment B raw6349 raw6349Labels = mixedMoment B raw6349step0 raw6349step0Labels := by
      have hz : ∀ j, raw6349 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6349step0 = (fun i j => raw6349 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6349step0 raw6349; decide +kernel
      have hl : raw6349step0Labels = raw6349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6349 raw6349Labels permutation346 hz
    mixedMoment B raw6349step0 raw6349step0Labels = mixedMoment B raw6349step1 raw6349step1Labels := by
      have ha : raw6349step1 = (fun i j => raw6349step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6349step1 raw6349step0; decide +kernel
      have hl : raw6349step1Labels = raw6349step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6349step0 raw6349step0Labels permutation38 permutation2
    _ = mixedMoment B node1394 node1394Labels := by rfl

def raw6350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6350Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6350step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw6350step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6350 raw6350Labels = mixedMoment B node2984 node2984Labels := by
  calc
    mixedMoment B raw6350 raw6350Labels = mixedMoment B raw6350step0 raw6350step0Labels := by
      have ha : raw6350step0 = (fun i j => raw6350 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6350step0 raw6350; decide +kernel
      have hl : raw6350step0Labels = raw6350Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6350 raw6350Labels permutation184 permutation2
    _ = mixedMoment B node2984 node2984Labels := by rfl

def raw6351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6351Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6351step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw6351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6351 raw6351Labels = mixedMoment B node2954 node2954Labels := by
  calc
    mixedMoment B raw6351 raw6351Labels = mixedMoment B raw6351step0 raw6351step0Labels := by
      have hz : ∀ j, raw6351 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6351step0 = (fun i j => raw6351 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6351step0 raw6351; decide +kernel
      have hl : raw6351step0Labels = raw6351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6351 raw6351Labels permutation346 hz
    mixedMoment B raw6351step0 raw6351step0Labels = mixedMoment B raw6351step1 raw6351step1Labels := by
      have ha : raw6351step1 = (fun i j => raw6351step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6351step1 raw6351step0; decide +kernel
      have hl : raw6351step1Labels = raw6351step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6351step0 raw6351step0Labels permutation40 permutation2
    _ = mixedMoment B node2954 node2954Labels := by rfl

def raw6352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6352Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6352step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw6352step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6352 raw6352Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw6352 raw6352Labels = mixedMoment B raw6352step0 raw6352step0Labels := by
      have hz : ∀ j, raw6352 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6352step0 = (fun i j => raw6352 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6352step0 raw6352; decide +kernel
      have hl : raw6352step0Labels = raw6352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6352 raw6352Labels permutation346 hz
    mixedMoment B raw6352step0 raw6352step0Labels = mixedMoment B raw6352step1 raw6352step1Labels := by
      have ha : raw6352step1 = (fun i j => raw6352step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6352step1 raw6352step0; decide +kernel
      have hl : raw6352step1Labels = raw6352step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6352step0 raw6352step0Labels permutation40 permutation2
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw6353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6353Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6353step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw6353step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6353 raw6353Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw6353 raw6353Labels = mixedMoment B raw6353step0 raw6353step0Labels := by
      have hz : ∀ j, raw6353 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6353step0 = (fun i j => raw6353 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6353step0 raw6353; decide +kernel
      have hl : raw6353step0Labels = raw6353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6353 raw6353Labels permutation346 hz
    mixedMoment B raw6353step0 raw6353step0Labels = mixedMoment B raw6353step1 raw6353step1Labels := by
      have ha : raw6353step1 = (fun i j => raw6353step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6353step1 raw6353step0; decide +kernel
      have hl : raw6353step1Labels = raw6353step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6353step0 raw6353step0Labels permutation40 permutation2
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw6354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6354Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6354step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6354 raw6354Labels = mixedMoment B node3013 node3013Labels := by
  calc
    mixedMoment B raw6354 raw6354Labels = mixedMoment B raw6354step0 raw6354step0Labels := by
      have ha : raw6354step0 = (fun i j => raw6354 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6354step0 raw6354; decide +kernel
      have hl : raw6354step0Labels = raw6354Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6354 raw6354Labels permutation160 permutation2
    _ = mixedMoment B node3013 node3013Labels := by rfl

def raw6355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6355Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6355step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6355 raw6355Labels = mixedMoment B node3014 node3014Labels := by
  calc
    mixedMoment B raw6355 raw6355Labels = mixedMoment B raw6355step0 raw6355step0Labels := by
      have hz : ∀ j, raw6355 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6355step0 = (fun i j => raw6355 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6355step0 raw6355; decide +kernel
      have hl : raw6355step0Labels = raw6355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6355 raw6355Labels permutation346 hz
    _ = mixedMoment B node3014 node3014Labels := by rfl

def raw6356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6356step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw6356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6356 raw6356Labels = mixedMoment B node2949 node2949Labels := by
  calc
    mixedMoment B raw6356 raw6356Labels = mixedMoment B raw6356step0 raw6356step0Labels := by
      have hz : ∀ j, raw6356 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6356step0 = (fun i j => raw6356 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6356step0 raw6356; decide +kernel
      have hl : raw6356step0Labels = raw6356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6356 raw6356Labels permutation346 hz
    mixedMoment B raw6356step0 raw6356step0Labels = mixedMoment B raw6356step1 raw6356step1Labels := by
      have ha : raw6356step1 = (fun i j => raw6356step0 (permutation120 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6356step1 raw6356step0; decide +kernel
      have hl : raw6356step1Labels = raw6356step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6356step0 raw6356step0Labels permutation120 permutation4
    _ = mixedMoment B node2949 node2949Labels := by rfl

def raw6357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6357Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6357step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 2, 1]]
def raw6357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6357step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw6357step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6357 raw6357Labels = mixedMoment B node2624 node2624Labels := by
  calc
    mixedMoment B raw6357 raw6357Labels = mixedMoment B raw6357step0 raw6357step0Labels := by
      have hz : ∀ j, raw6357 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6357step0 = (fun i j => raw6357 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6357step0 raw6357; decide +kernel
      have hl : raw6357step0Labels = raw6357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6357 raw6357Labels permutation346 hz
    mixedMoment B raw6357step0 raw6357step0Labels = mixedMoment B raw6357step1 raw6357step1Labels := by
      have ha : raw6357step1 = (fun i j => raw6357step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6357step1 raw6357step0; decide +kernel
      have hl : raw6357step1Labels = raw6357step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6357step0 raw6357step0Labels permutation151 permutation2
    mixedMoment B raw6357step1 raw6357step1Labels = mixedMoment B raw6357step2 raw6357step2Labels := by
      have ha : raw6357step2 = -raw6357step1 := by apply Matrix.ext; change ∀ i j, raw6357step2 i j = -(raw6357step1 i j); unfold raw6357step2 raw6357step1; decide +kernel
      have hl : raw6357step2Labels = raw6357step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2624 node2624Labels := by rfl

def raw6358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6358Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6358step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw6358step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6358 raw6358Labels = mixedMoment B node2933 node2933Labels := by
  calc
    mixedMoment B raw6358 raw6358Labels = mixedMoment B raw6358step0 raw6358step0Labels := by
      have ha : raw6358step0 = (fun i j => raw6358 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6358step0 raw6358; decide +kernel
      have hl : raw6358step0Labels = raw6358Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6358 raw6358Labels permutation202 permutation2
    _ = mixedMoment B node2933 node2933Labels := by rfl

def raw6359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6359Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6359 raw6359Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw6359 raw6359Labels = mixedMoment B raw6359step0 raw6359step0Labels := by
      have ha : raw6359step0 = (fun i j => raw6359 (permutation212 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6359step0 raw6359; decide +kernel
      have hl : raw6359step0Labels = raw6359Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6359 raw6359Labels permutation212 permutation2
    _ = mixedMoment B node3064 node3064Labels := by rfl

def raw6360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6360Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6360 raw6360Labels = mixedMoment B node3084 node3084Labels := by
  calc
    mixedMoment B raw6360 raw6360Labels = mixedMoment B raw6360step0 raw6360step0Labels := by
      have ha : raw6360step0 = (fun i j => raw6360 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6360step0 raw6360; decide +kernel
      have hl : raw6360step0Labels = raw6360Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6360 raw6360Labels permutation202 permutation2
    _ = mixedMoment B node3084 node3084Labels := by rfl

def raw6361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6361Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw6361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6361 raw6361Labels = mixedMoment B node2992 node2992Labels := by
  calc
    mixedMoment B raw6361 raw6361Labels = mixedMoment B raw6361step0 raw6361step0Labels := by
      have ha : raw6361step0 = (fun i j => raw6361 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6361step0 raw6361; decide +kernel
      have hl : raw6361step0Labels = raw6361Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6361 raw6361Labels permutation176 permutation2
    _ = mixedMoment B node2992 node2992Labels := by rfl

def raw6362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6362Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw6362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6362 raw6362Labels = mixedMoment B node2947 node2947Labels := by
  calc
    mixedMoment B raw6362 raw6362Labels = mixedMoment B raw6362step0 raw6362step0Labels := by
      have ha : raw6362step0 = (fun i j => raw6362 (permutation568 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6362step0 raw6362; decide +kernel
      have hl : raw6362step0Labels = raw6362Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6362 raw6362Labels permutation568 permutation4
    _ = mixedMoment B node2947 node2947Labels := by rfl

def raw6363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6363Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw6363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6363step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw6363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6363 raw6363Labels = mixedMoment B node2610 node2610Labels := by
  calc
    mixedMoment B raw6363 raw6363Labels = mixedMoment B raw6363step0 raw6363step0Labels := by
      have ha : raw6363step0 = (fun i j => raw6363 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6363step0 raw6363; decide +kernel
      have hl : raw6363step0Labels = raw6363Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6363 raw6363Labels permutation676 permutation2
    mixedMoment B raw6363step0 raw6363step0Labels = mixedMoment B raw6363step1 raw6363step1Labels := by
      have ha : raw6363step1 = -raw6363step0 := by apply Matrix.ext; change ∀ i j, raw6363step1 i j = -(raw6363step0 i j); unfold raw6363step1 raw6363step0; decide +kernel
      have hl : raw6363step1Labels = raw6363step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2610 node2610Labels := by rfl

def raw6364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw6364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6364 raw6364Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw6364 raw6364Labels = mixedMoment B raw6364step0 raw6364step0Labels := by
      have hz : ∀ j, raw6364 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6364step0 = (fun i j => raw6364 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6364step0 raw6364; decide +kernel
      have hl : raw6364step0Labels = raw6364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6364 raw6364Labels permutation346 hz
    mixedMoment B raw6364step0 raw6364step0Labels = mixedMoment B raw6364step1 raw6364step1Labels := by
      have ha : raw6364step1 = (fun i j => raw6364step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6364step1 raw6364step0; decide +kernel
      have hl : raw6364step1Labels = raw6364step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6364step0 raw6364step0Labels permutation44 permutation2
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw6365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6365Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw6365step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6365 raw6365Labels = mixedMoment B node3108 node3108Labels := by
  calc
    mixedMoment B raw6365 raw6365Labels = mixedMoment B raw6365step0 raw6365step0Labels := by
      have hz : ∀ j, raw6365 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6365step0 = (fun i j => raw6365 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6365step0 raw6365; decide +kernel
      have hl : raw6365step0Labels = raw6365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6365 raw6365Labels permutation346 hz
    _ = mixedMoment B node3108 node3108Labels := by rfl

def raw6366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![2, -3, 1], ![2, 0, -2]]
def raw6366step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw6366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6366 raw6366Labels = mixedMoment B node2942 node2942Labels := by
  calc
    mixedMoment B raw6366 raw6366Labels = mixedMoment B raw6366step0 raw6366step0Labels := by
      have hz : ∀ j, raw6366 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6366step0 = (fun i j => raw6366 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6366step0 raw6366; decide +kernel
      have hl : raw6366step0Labels = raw6366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6366 raw6366Labels permutation346 hz
    mixedMoment B raw6366step0 raw6366step0Labels = mixedMoment B raw6366step1 raw6366step1Labels := by
      have ha : raw6366step1 = (fun i j => raw6366step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6366step1 raw6366step0; decide +kernel
      have hl : raw6366step1Labels = raw6366step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6366step0 raw6366step0Labels permutation38 permutation2
    _ = mixedMoment B node2942 node2942Labels := by rfl

def raw6367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![3, -1, -2]]
def raw6367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 2, 1]]
def raw6367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6367step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw6367step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6367 raw6367Labels = mixedMoment B node2618 node2618Labels := by
  calc
    mixedMoment B raw6367 raw6367Labels = mixedMoment B raw6367step0 raw6367step0Labels := by
      have hz : ∀ j, raw6367 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6367step0 = (fun i j => raw6367 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6367step0 raw6367; decide +kernel
      have hl : raw6367step0Labels = raw6367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6367 raw6367Labels permutation346 hz
    mixedMoment B raw6367step0 raw6367step0Labels = mixedMoment B raw6367step1 raw6367step1Labels := by
      have ha : raw6367step1 = (fun i j => raw6367step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6367step1 raw6367step0; decide +kernel
      have hl : raw6367step1Labels = raw6367step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6367step0 raw6367step0Labels permutation149 permutation2
    mixedMoment B raw6367step1 raw6367step1Labels = mixedMoment B raw6367step2 raw6367step2Labels := by
      have ha : raw6367step2 = -raw6367step1 := by apply Matrix.ext; change ∀ i j, raw6367step2 i j = -(raw6367step1 i j); unfold raw6367step2 raw6367step1; decide +kernel
      have hl : raw6367step2Labels = raw6367step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2618 node2618Labels := by rfl

def raw6368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -3, 1], ![1, 1, -2]]
def raw6368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![1, 1, -2]]
def raw6368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6368 raw6368Labels = mixedMoment B node2964 node2964Labels := by
  calc
    mixedMoment B raw6368 raw6368Labels = mixedMoment B raw6368step0 raw6368step0Labels := by
      have hz : ∀ j, raw6368 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6368step0 = (fun i j => raw6368 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6368step0 raw6368; decide +kernel
      have hl : raw6368step0Labels = raw6368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6368 raw6368Labels permutation346 hz
    mixedMoment B raw6368step0 raw6368step0Labels = mixedMoment B raw6368step1 raw6368step1Labels := by
      have ha : raw6368step1 = (fun i j => raw6368step0 (permutation119 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6368step1 raw6368step0; decide +kernel
      have hl : raw6368step1Labels = raw6368step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6368step0 raw6368step0Labels permutation119 permutation4
    _ = mixedMoment B node2964 node2964Labels := by rfl

def raw6369 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6369Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6369step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6369step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6369step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw6369step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6369 raw6369Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw6369 raw6369Labels = mixedMoment B raw6369step0 raw6369step0Labels := by
      have hz : ∀ j, raw6369 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6369step0 = (fun i j => raw6369 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6369step0 raw6369; decide +kernel
      have hl : raw6369step0Labels = raw6369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6369 raw6369Labels permutation346 hz
    mixedMoment B raw6369step0 raw6369step0Labels = mixedMoment B raw6369step1 raw6369step1Labels := by
      have ha : raw6369step1 = (fun i j => raw6369step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6369step1 raw6369step0; decide +kernel
      have hl : raw6369step1Labels = raw6369step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6369step0 raw6369step0Labels permutation38 permutation7
    mixedMoment B raw6369step1 raw6369step1Labels = mixedMoment B raw6369step2 raw6369step2Labels := by
      have ha : raw6369step2 = raw6369step1 := by apply Matrix.ext; unfold raw6369step2 raw6369step1; decide +kernel
      have hl : raw6369step1Labels = labelEmbedding10 ∘ raw6369step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6369step1 raw6369step1Labels raw6369step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

def raw6370 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6370Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6370step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6370step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6370 raw6370Labels = mixedMoment B node5249 node5249Labels := by
  calc
    mixedMoment B raw6370 raw6370Labels = mixedMoment B raw6370step0 raw6370step0Labels := by
      have ha : raw6370step0 = (fun i j => raw6370 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6370step0 raw6370; decide +kernel
      have hl : raw6370step0Labels = raw6370Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6370 raw6370Labels permutation200 permutation7
    mixedMoment B raw6370step0 raw6370step0Labels = mixedMoment B raw6370step1 raw6370step1Labels := by
      have ha : raw6370step1 = raw6370step0 := by apply Matrix.ext; unfold raw6370step1 raw6370step0; decide +kernel
      have hl : raw6370step0Labels = labelEmbedding10 ∘ raw6370step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6370step0 raw6370step0Labels raw6370step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5249 node5249Labels := by rfl

def raw6371 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6371Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6371step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6371step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6371step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6371step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6371 raw6371Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw6371 raw6371Labels = mixedMoment B raw6371step0 raw6371step0Labels := by
      have hz : ∀ j, raw6371 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6371step0 = (fun i j => raw6371 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6371step0 raw6371; decide +kernel
      have hl : raw6371step0Labels = raw6371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6371 raw6371Labels permutation346 hz
    mixedMoment B raw6371step0 raw6371step0Labels = mixedMoment B raw6371step1 raw6371step1Labels := by
      have ha : raw6371step1 = (fun i j => raw6371step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6371step1 raw6371step0; decide +kernel
      have hl : raw6371step1Labels = raw6371step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6371step0 raw6371step0Labels permutation38 permutation7
    mixedMoment B raw6371step1 raw6371step1Labels = mixedMoment B raw6371step2 raw6371step2Labels := by
      have ha : raw6371step2 = raw6371step1 := by apply Matrix.ext; unfold raw6371step2 raw6371step1; decide +kernel
      have hl : raw6371step1Labels = labelEmbedding10 ∘ raw6371step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6371step1 raw6371step1Labels raw6371step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw6372 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6372Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6372step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw6372step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6372 raw6372Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw6372 raw6372Labels = mixedMoment B raw6372step0 raw6372step0Labels := by
      have hz : ∀ j, raw6372 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6372step0 = (fun i j => raw6372 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6372step0 raw6372; decide +kernel
      have hl : raw6372step0Labels = raw6372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6372 raw6372Labels permutation346 hz
    mixedMoment B raw6372step0 raw6372step0Labels = mixedMoment B raw6372step1 raw6372step1Labels := by
      have ha : raw6372step1 = (fun i j => raw6372step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6372step1 raw6372step0; decide +kernel
      have hl : raw6372step1Labels = raw6372step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6372step0 raw6372step0Labels permutation139 permutation2
    _ = mixedMoment B node5161 node5161Labels := by rfl

def raw6373 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6373step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6373step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6373step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6373step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6373step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6373step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6373step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6373 raw6373Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw6373 raw6373Labels = mixedMoment B raw6373step0 raw6373step0Labels := by
      have hz : ∀ j, raw6373 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6373step0 = (fun i j => raw6373 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6373step0 raw6373; decide +kernel
      have hl : raw6373step0Labels = raw6373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6373 raw6373Labels permutation346 hz
    mixedMoment B raw6373step0 raw6373step0Labels = mixedMoment B raw6373step1 raw6373step1Labels := by
      have hz : ∀ j, raw6373step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6373step1 = (fun i j => raw6373step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6373step1 raw6373step0; decide +kernel
      have hl : raw6373step1Labels = raw6373step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6373step0 raw6373step0Labels permutation56 hz
    mixedMoment B raw6373step1 raw6373step1Labels = mixedMoment B raw6373step2 raw6373step2Labels := by
      have ha : raw6373step2 = (fun i j => raw6373step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6373step2 raw6373step1; decide +kernel
      have hl : raw6373step2Labels = raw6373step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6373step1 raw6373step1Labels permutation8 permutation6
    mixedMoment B raw6373step2 raw6373step2Labels = mixedMoment B raw6373step3 raw6373step3Labels := by
      have ha : raw6373step3 = raw6373step2 := by apply Matrix.ext; unfold raw6373step3 raw6373step2; decide +kernel
      have hl : raw6373step2Labels = labelEmbedding9 ∘ raw6373step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6373step2 raw6373step2Labels raw6373step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw6374 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6374step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6374step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6374step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6374step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6374 raw6374Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw6374 raw6374Labels = mixedMoment B raw6374step0 raw6374step0Labels := by
      have hz : ∀ j, raw6374 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw6374step0 = (fun i j => raw6374 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw6374step0 raw6374; decide +kernel
      have hl : raw6374step0Labels = raw6374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6374 raw6374Labels permutation265 hz
    mixedMoment B raw6374step0 raw6374step0Labels = mixedMoment B raw6374step1 raw6374step1Labels := by
      have ha : raw6374step1 = (fun i j => raw6374step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6374step1 raw6374step0; decide +kernel
      have hl : raw6374step1Labels = raw6374step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6374step0 raw6374step0Labels permutation32 permutation6
    mixedMoment B raw6374step1 raw6374step1Labels = mixedMoment B raw6374step2 raw6374step2Labels := by
      have ha : raw6374step2 = raw6374step1 := by apply Matrix.ext; unfold raw6374step2 raw6374step1; decide +kernel
      have hl : raw6374step1Labels = labelEmbedding9 ∘ raw6374step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6374step1 raw6374step1Labels raw6374step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw6375 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6375step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6375step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6375step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6375step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6375step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6375step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6375 raw6375Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw6375 raw6375Labels = mixedMoment B raw6375step0 raw6375step0Labels := by
      have hz : ∀ j, raw6375 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6375step0 = (fun i j => raw6375 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6375step0 raw6375; decide +kernel
      have hl : raw6375step0Labels = raw6375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6375 raw6375Labels permutation346 hz
    mixedMoment B raw6375step0 raw6375step0Labels = mixedMoment B raw6375step1 raw6375step1Labels := by
      have hz : ∀ j, raw6375step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6375step1 = (fun i j => raw6375step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6375step1 raw6375step0; decide +kernel
      have hl : raw6375step1Labels = raw6375step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6375step0 raw6375step0Labels permutation56 hz
    mixedMoment B raw6375step1 raw6375step1Labels = mixedMoment B raw6375step2 raw6375step2Labels := by
      have ha : raw6375step2 = (fun i j => raw6375step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6375step2 raw6375step1; decide +kernel
      have hl : raw6375step2Labels = raw6375step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6375step1 raw6375step1Labels permutation8 permutation6
    mixedMoment B raw6375step2 raw6375step2Labels = mixedMoment B raw6375step3 raw6375step3Labels := by
      have ha : raw6375step3 = raw6375step2 := by apply Matrix.ext; unfold raw6375step3 raw6375step2; decide +kernel
      have hl : raw6375step2Labels = labelEmbedding9 ∘ raw6375step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6375step2 raw6375step2Labels raw6375step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw6376 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6376step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6376step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6376step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6376step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6376step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6376step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6376step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6376 raw6376Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw6376 raw6376Labels = mixedMoment B raw6376step0 raw6376step0Labels := by
      have hz : ∀ j, raw6376 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6376step0 = (fun i j => raw6376 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6376step0 raw6376; decide +kernel
      have hl : raw6376step0Labels = raw6376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6376 raw6376Labels permutation346 hz
    mixedMoment B raw6376step0 raw6376step0Labels = mixedMoment B raw6376step1 raw6376step1Labels := by
      have hz : ∀ j, raw6376step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6376step1 = (fun i j => raw6376step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6376step1 raw6376step0; decide +kernel
      have hl : raw6376step1Labels = raw6376step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6376step0 raw6376step0Labels permutation56 hz
    mixedMoment B raw6376step1 raw6376step1Labels = mixedMoment B raw6376step2 raw6376step2Labels := by
      have ha : raw6376step2 = (fun i j => raw6376step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6376step2 raw6376step1; decide +kernel
      have hl : raw6376step2Labels = raw6376step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6376step1 raw6376step1Labels permutation8 permutation6
    mixedMoment B raw6376step2 raw6376step2Labels = mixedMoment B raw6376step3 raw6376step3Labels := by
      have ha : raw6376step3 = raw6376step2 := by apply Matrix.ext; unfold raw6376step3 raw6376step2; decide +kernel
      have hl : raw6376step2Labels = labelEmbedding9 ∘ raw6376step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6376step2 raw6376step2Labels raw6376step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw6377 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw6377step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6377step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6377step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6377step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6377 raw6377Labels = mixedMoment B node4815 node4815Labels := by
  calc
    mixedMoment B raw6377 raw6377Labels = mixedMoment B raw6377step0 raw6377step0Labels := by
      have ha : raw6377step0 = (fun i j => raw6377 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6377step0 raw6377; decide +kernel
      have hl : raw6377step0Labels = raw6377Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6377 raw6377Labels permutation170 permutation4
    mixedMoment B raw6377step0 raw6377step0Labels = mixedMoment B raw6377step1 raw6377step1Labels := by
      have ha : raw6377step1 = -raw6377step0 := by apply Matrix.ext; change ∀ i j, raw6377step1 i j = -(raw6377step0 i j); unfold raw6377step1 raw6377step0; decide +kernel
      have hl : raw6377step1Labels = raw6377step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6377step1 raw6377step1Labels = mixedMoment B raw6377step2 raw6377step2Labels := by
      have ha : raw6377step2 = raw6377step1 := by apply Matrix.ext; unfold raw6377step2 raw6377step1; decide +kernel
      have hl : raw6377step1Labels = labelEmbedding7 ∘ raw6377step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6377step1 raw6377step1Labels raw6377step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4815 node4815Labels := by rfl

def raw6378 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6378step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6378step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6378step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6378 raw6378Labels = mixedMoment B node5221 node5221Labels := by
  calc
    mixedMoment B raw6378 raw6378Labels = mixedMoment B raw6378step0 raw6378step0Labels := by
      have ha : raw6378step0 = (fun i j => raw6378 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6378step0 raw6378; decide +kernel
      have hl : raw6378step0Labels = raw6378Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6378 raw6378Labels permutation152 permutation6
    mixedMoment B raw6378step0 raw6378step0Labels = mixedMoment B raw6378step1 raw6378step1Labels := by
      have ha : raw6378step1 = raw6378step0 := by apply Matrix.ext; unfold raw6378step1 raw6378step0; decide +kernel
      have hl : raw6378step0Labels = labelEmbedding9 ∘ raw6378step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6378step0 raw6378step0Labels raw6378step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5221 node5221Labels := by rfl

def raw6379 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6379step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6379step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6379 raw6379Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw6379 raw6379Labels = mixedMoment B raw6379step0 raw6379step0Labels := by
      have ha : raw6379step0 = (fun i j => raw6379 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6379step0 raw6379; decide +kernel
      have hl : raw6379step0Labels = raw6379Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6379 raw6379Labels permutation152 permutation6
    mixedMoment B raw6379step0 raw6379step0Labels = mixedMoment B raw6379step1 raw6379step1Labels := by
      have ha : raw6379step1 = raw6379step0 := by apply Matrix.ext; unfold raw6379step1 raw6379step0; decide +kernel
      have hl : raw6379step0Labels = labelEmbedding9 ∘ raw6379step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6379step0 raw6379step0Labels raw6379step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw6380 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw6380step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6380 raw6380Labels = mixedMoment B node5159 node5159Labels := by
  calc
    mixedMoment B raw6380 raw6380Labels = mixedMoment B raw6380step0 raw6380step0Labels := by
      have ha : raw6380step0 = (fun i j => raw6380 (permutation620 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6380step0 raw6380; decide +kernel
      have hl : raw6380step0Labels = raw6380Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6380 raw6380Labels permutation620 permutation2
    _ = mixedMoment B node5159 node5159Labels := by rfl

def raw6381 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw6381step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6381step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6381step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6381step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6381step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6381 raw6381Labels = mixedMoment B node4821 node4821Labels := by
  calc
    mixedMoment B raw6381 raw6381Labels = mixedMoment B raw6381step0 raw6381step0Labels := by
      have hz : ∀ j, raw6381 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6381step0 = (fun i j => raw6381 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6381step0 raw6381; decide +kernel
      have hl : raw6381step0Labels = raw6381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6381 raw6381Labels permutation346 hz
    mixedMoment B raw6381step0 raw6381step0Labels = mixedMoment B raw6381step1 raw6381step1Labels := by
      have ha : raw6381step1 = (fun i j => raw6381step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6381step1 raw6381step0; decide +kernel
      have hl : raw6381step1Labels = raw6381step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6381step0 raw6381step0Labels permutation36 permutation4
    mixedMoment B raw6381step1 raw6381step1Labels = mixedMoment B raw6381step2 raw6381step2Labels := by
      have ha : raw6381step2 = -raw6381step1 := by apply Matrix.ext; change ∀ i j, raw6381step2 i j = -(raw6381step1 i j); unfold raw6381step2 raw6381step1; decide +kernel
      have hl : raw6381step2Labels = raw6381step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6381step2 raw6381step2Labels = mixedMoment B raw6381step3 raw6381step3Labels := by
      have ha : raw6381step3 = raw6381step2 := by apply Matrix.ext; unfold raw6381step3 raw6381step2; decide +kernel
      have hl : raw6381step2Labels = labelEmbedding7 ∘ raw6381step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6381step2 raw6381step2Labels raw6381step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4821 node4821Labels := by rfl

def raw6382 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6382step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6382step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6382step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6382step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6382 raw6382Labels = mixedMoment B node5234 node5234Labels := by
  calc
    mixedMoment B raw6382 raw6382Labels = mixedMoment B raw6382step0 raw6382step0Labels := by
      have hz : ∀ j, raw6382 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6382step0 = (fun i j => raw6382 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6382step0 raw6382; decide +kernel
      have hl : raw6382step0Labels = raw6382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6382 raw6382Labels permutation346 hz
    mixedMoment B raw6382step0 raw6382step0Labels = mixedMoment B raw6382step1 raw6382step1Labels := by
      have ha : raw6382step1 = (fun i j => raw6382step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6382step1 raw6382step0; decide +kernel
      have hl : raw6382step1Labels = raw6382step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6382step0 raw6382step0Labels permutation32 permutation6
    mixedMoment B raw6382step1 raw6382step1Labels = mixedMoment B raw6382step2 raw6382step2Labels := by
      have ha : raw6382step2 = raw6382step1 := by apply Matrix.ext; unfold raw6382step2 raw6382step1; decide +kernel
      have hl : raw6382step1Labels = labelEmbedding9 ∘ raw6382step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6382step1 raw6382step1Labels raw6382step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5234 node5234Labels := by rfl

def raw6383 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6383step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6383step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6383step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6383 raw6383Labels = mixedMoment B node5245 node5245Labels := by
  calc
    mixedMoment B raw6383 raw6383Labels = mixedMoment B raw6383step0 raw6383step0Labels := by
      have ha : raw6383step0 = (fun i j => raw6383 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6383step0 raw6383; decide +kernel
      have hl : raw6383step0Labels = raw6383Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6383 raw6383Labels permutation152 permutation6
    mixedMoment B raw6383step0 raw6383step0Labels = mixedMoment B raw6383step1 raw6383step1Labels := by
      have ha : raw6383step1 = raw6383step0 := by apply Matrix.ext; unfold raw6383step1 raw6383step0; decide +kernel
      have hl : raw6383step0Labels = labelEmbedding9 ∘ raw6383step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6383step0 raw6383step0Labels raw6383step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5245 node5245Labels := by rfl

def raw6384 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6384step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6384step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6384step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6384 raw6384Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw6384 raw6384Labels = mixedMoment B raw6384step0 raw6384step0Labels := by
      have hz : ∀ j, raw6384 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6384step0 = (fun i j => raw6384 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6384step0 raw6384; decide +kernel
      have hl : raw6384step0Labels = raw6384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6384 raw6384Labels permutation346 hz
    mixedMoment B raw6384step0 raw6384step0Labels = mixedMoment B raw6384step1 raw6384step1Labels := by
      have ha : raw6384step1 = (fun i j => raw6384step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6384step1 raw6384step0; decide +kernel
      have hl : raw6384step1Labels = raw6384step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6384step0 raw6384step0Labels permutation32 permutation6
    mixedMoment B raw6384step1 raw6384step1Labels = mixedMoment B raw6384step2 raw6384step2Labels := by
      have ha : raw6384step2 = raw6384step1 := by apply Matrix.ext; unfold raw6384step2 raw6384step1; decide +kernel
      have hl : raw6384step1Labels = labelEmbedding9 ∘ raw6384step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6384step1 raw6384step1Labels raw6384step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw6385 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6385step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6385 raw6385Labels = mixedMoment B node5165 node5165Labels := by
  calc
    mixedMoment B raw6385 raw6385Labels = mixedMoment B raw6385step0 raw6385step0Labels := by
      have hz : ∀ j, raw6385 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6385step0 = (fun i j => raw6385 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6385step0 raw6385; decide +kernel
      have hl : raw6385step0Labels = raw6385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6385 raw6385Labels permutation346 hz
    mixedMoment B raw6385step0 raw6385step0Labels = mixedMoment B raw6385step1 raw6385step1Labels := by
      have ha : raw6385step1 = (fun i j => raw6385step0 (permutation138 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6385step1 raw6385step0; decide +kernel
      have hl : raw6385step1Labels = raw6385step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6385step0 raw6385step0Labels permutation138 permutation2
    _ = mixedMoment B node5165 node5165Labels := by rfl

def raw6386 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6386step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6386step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6386step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6386step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6386step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw6386step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6386 raw6386Labels = mixedMoment B node5276 node5276Labels := by
  calc
    mixedMoment B raw6386 raw6386Labels = mixedMoment B raw6386step0 raw6386step0Labels := by
      have hz : ∀ j, raw6386 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6386step0 = (fun i j => raw6386 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6386step0 raw6386; decide +kernel
      have hl : raw6386step0Labels = raw6386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6386 raw6386Labels permutation434 hz
    mixedMoment B raw6386step0 raw6386step0Labels = mixedMoment B raw6386step1 raw6386step1Labels := by
      have hz : ∀ j, raw6386step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6386step1 = (fun i j => raw6386step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6386step1 raw6386step0; decide +kernel
      have hl : raw6386step1Labels = raw6386step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6386step0 raw6386step0Labels permutation80 hz
    mixedMoment B raw6386step1 raw6386step1Labels = mixedMoment B raw6386step2 raw6386step2Labels := by
      have ha : raw6386step2 = (fun i j => raw6386step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6386step2 raw6386step1; decide +kernel
      have hl : raw6386step2Labels = raw6386step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6386step1 raw6386step1Labels permutation8 permutation6
    mixedMoment B raw6386step2 raw6386step2Labels = mixedMoment B raw6386step3 raw6386step3Labels := by
      have ha : raw6386step3 = raw6386step2 := by apply Matrix.ext; unfold raw6386step3 raw6386step2; decide +kernel
      have hl : raw6386step2Labels = labelEmbedding9 ∘ raw6386step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6386step2 raw6386step2Labels raw6386step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5276 node5276Labels := by rfl

def raw6387 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6387step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw6387step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6387step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6387step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6387step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6387step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6387 raw6387Labels = mixedMoment B node4835 node4835Labels := by
  calc
    mixedMoment B raw6387 raw6387Labels = mixedMoment B raw6387step0 raw6387step0Labels := by
      have hz : ∀ j, raw6387 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6387step0 = (fun i j => raw6387 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6387step0 raw6387; decide +kernel
      have hl : raw6387step0Labels = raw6387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6387 raw6387Labels permutation346 hz
    mixedMoment B raw6387step0 raw6387step0Labels = mixedMoment B raw6387step1 raw6387step1Labels := by
      have ha : raw6387step1 = (fun i j => raw6387step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6387step1 raw6387step0; decide +kernel
      have hl : raw6387step1Labels = raw6387step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6387step0 raw6387step0Labels permutation33 permutation4
    mixedMoment B raw6387step1 raw6387step1Labels = mixedMoment B raw6387step2 raw6387step2Labels := by
      have ha : raw6387step2 = -raw6387step1 := by apply Matrix.ext; change ∀ i j, raw6387step2 i j = -(raw6387step1 i j); unfold raw6387step2 raw6387step1; decide +kernel
      have hl : raw6387step2Labels = raw6387step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6387step2 raw6387step2Labels = mixedMoment B raw6387step3 raw6387step3Labels := by
      have ha : raw6387step3 = raw6387step2 := by apply Matrix.ext; unfold raw6387step3 raw6387step2; decide +kernel
      have hl : raw6387step2Labels = labelEmbedding7 ∘ raw6387step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6387step2 raw6387step2Labels raw6387step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4835 node4835Labels := by rfl

def raw6388 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6388step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6388step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6388step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6388 raw6388Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw6388 raw6388Labels = mixedMoment B raw6388step0 raw6388step0Labels := by
      have hz : ∀ j, raw6388 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6388step0 = (fun i j => raw6388 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6388step0 raw6388; decide +kernel
      have hl : raw6388step0Labels = raw6388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6388 raw6388Labels permutation346 hz
    mixedMoment B raw6388step0 raw6388step0Labels = mixedMoment B raw6388step1 raw6388step1Labels := by
      have ha : raw6388step1 = (fun i j => raw6388step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6388step1 raw6388step0; decide +kernel
      have hl : raw6388step1Labels = raw6388step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6388step0 raw6388step0Labels permutation32 permutation6
    mixedMoment B raw6388step1 raw6388step1Labels = mixedMoment B raw6388step2 raw6388step2Labels := by
      have ha : raw6388step2 = raw6388step1 := by apply Matrix.ext; unfold raw6388step2 raw6388step1; decide +kernel
      have hl : raw6388step1Labels = labelEmbedding9 ∘ raw6388step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6388step1 raw6388step1Labels raw6388step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5229 node5229Labels := by rfl

def raw6389 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw6389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6389step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6389step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6389 raw6389Labels = mixedMoment B node5242 node5242Labels := by
  calc
    mixedMoment B raw6389 raw6389Labels = mixedMoment B raw6389step0 raw6389step0Labels := by
      have ha : raw6389step0 = (fun i j => raw6389 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6389step0 raw6389; decide +kernel
      have hl : raw6389step0Labels = raw6389Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6389 raw6389Labels permutation152 permutation6
    mixedMoment B raw6389step0 raw6389step0Labels = mixedMoment B raw6389step1 raw6389step1Labels := by
      have ha : raw6389step1 = raw6389step0 := by apply Matrix.ext; unfold raw6389step1 raw6389step0; decide +kernel
      have hl : raw6389step0Labels = labelEmbedding9 ∘ raw6389step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6389step0 raw6389step0Labels raw6389step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5242 node5242Labels := by rfl

def raw6390 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw6390step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6390step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6390step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6390step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6390step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6390 raw6390Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw6390 raw6390Labels = mixedMoment B raw6390step0 raw6390step0Labels := by
      have hz : ∀ j, raw6390 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6390step0 = (fun i j => raw6390 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6390step0 raw6390; decide +kernel
      have hl : raw6390step0Labels = raw6390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6390 raw6390Labels permutation346 hz
    mixedMoment B raw6390step0 raw6390step0Labels = mixedMoment B raw6390step1 raw6390step1Labels := by
      have ha : raw6390step1 = (fun i j => raw6390step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6390step1 raw6390step0; decide +kernel
      have hl : raw6390step1Labels = raw6390step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6390step0 raw6390step0Labels permutation32 permutation6
    mixedMoment B raw6390step1 raw6390step1Labels = mixedMoment B raw6390step2 raw6390step2Labels := by
      have ha : raw6390step2 = raw6390step1 := by apply Matrix.ext; unfold raw6390step2 raw6390step1; decide +kernel
      have hl : raw6390step1Labels = labelEmbedding9 ∘ raw6390step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6390step1 raw6390step1Labels raw6390step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw6391 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6391Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6391step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6391step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6391 raw6391Labels = mixedMoment B node3040 node3040Labels := by
  calc
    mixedMoment B raw6391 raw6391Labels = mixedMoment B raw6391step0 raw6391step0Labels := by
      have hz : ∀ j, raw6391 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6391step0 = (fun i j => raw6391 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6391step0 raw6391; decide +kernel
      have hl : raw6391step0Labels = raw6391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6391 raw6391Labels permutation346 hz
    mixedMoment B raw6391step0 raw6391step0Labels = mixedMoment B raw6391step1 raw6391step1Labels := by
      have ha : raw6391step1 = (fun i j => raw6391step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6391step1 raw6391step0; decide +kernel
      have hl : raw6391step1Labels = raw6391step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6391step0 raw6391step0Labels permutation32 permutation6
    _ = mixedMoment B node3040 node3040Labels := by rfl

def raw6392 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6392Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6392step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6392 raw6392Labels = mixedMoment B node3066 node3066Labels := by
  calc
    mixedMoment B raw6392 raw6392Labels = mixedMoment B raw6392step0 raw6392step0Labels := by
      have ha : raw6392step0 = (fun i j => raw6392 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6392step0 raw6392; decide +kernel
      have hl : raw6392step0Labels = raw6392Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6392 raw6392Labels permutation152 permutation6
    _ = mixedMoment B node3066 node3066Labels := by rfl

def raw6393 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6393Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6393step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6393step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6393 raw6393Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw6393 raw6393Labels = mixedMoment B raw6393step0 raw6393step0Labels := by
      have hz : ∀ j, raw6393 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6393step0 = (fun i j => raw6393 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6393step0 raw6393; decide +kernel
      have hl : raw6393step0Labels = raw6393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6393 raw6393Labels permutation346 hz
    mixedMoment B raw6393step0 raw6393step0Labels = mixedMoment B raw6393step1 raw6393step1Labels := by
      have ha : raw6393step1 = (fun i j => raw6393step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6393step1 raw6393step0; decide +kernel
      have hl : raw6393step1Labels = raw6393step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6393step0 raw6393step0Labels permutation32 permutation6
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw6394 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6394Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6394step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6394step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6394 raw6394Labels = mixedMoment B node2964 node2964Labels := by
  calc
    mixedMoment B raw6394 raw6394Labels = mixedMoment B raw6394step0 raw6394step0Labels := by
      have hz : ∀ j, raw6394 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6394step0 = (fun i j => raw6394 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6394step0 raw6394; decide +kernel
      have hl : raw6394step0Labels = raw6394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6394 raw6394Labels permutation346 hz
    mixedMoment B raw6394step0 raw6394step0Labels = mixedMoment B raw6394step1 raw6394step1Labels := by
      have ha : raw6394step1 = (fun i j => raw6394step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6394step1 raw6394step0; decide +kernel
      have hl : raw6394step1Labels = raw6394step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6394step0 raw6394step0Labels permutation137 permutation3
    _ = mixedMoment B node2964 node2964Labels := by rfl

def raw6395 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6395Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6395step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6395step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6395step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6395step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6395step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6395 raw6395Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw6395 raw6395Labels = mixedMoment B raw6395step0 raw6395step0Labels := by
      have hz : ∀ j, raw6395 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6395step0 = (fun i j => raw6395 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6395step0 raw6395; decide +kernel
      have hl : raw6395step0Labels = raw6395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6395 raw6395Labels permutation346 hz
    mixedMoment B raw6395step0 raw6395step0Labels = mixedMoment B raw6395step1 raw6395step1Labels := by
      have hz : ∀ j, raw6395step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6395step1 = (fun i j => raw6395step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6395step1 raw6395step0; decide +kernel
      have hl : raw6395step1Labels = raw6395step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6395step0 raw6395step0Labels permutation56 hz
    mixedMoment B raw6395step1 raw6395step1Labels = mixedMoment B raw6395step2 raw6395step2Labels := by
      have ha : raw6395step2 = (fun i j => raw6395step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6395step2 raw6395step1; decide +kernel
      have hl : raw6395step2Labels = raw6395step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6395step1 raw6395step1Labels permutation8 permutation6
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw6396 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6396Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6396step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6396 raw6396Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw6396 raw6396Labels = mixedMoment B raw6396step0 raw6396step0Labels := by
      have hz : ∀ j, raw6396 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw6396step0 = (fun i j => raw6396 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw6396step0 raw6396; decide +kernel
      have hl : raw6396step0Labels = raw6396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6396 raw6396Labels permutation265 hz
    mixedMoment B raw6396step0 raw6396step0Labels = mixedMoment B raw6396step1 raw6396step1Labels := by
      have ha : raw6396step1 = (fun i j => raw6396step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6396step1 raw6396step0; decide +kernel
      have hl : raw6396step1Labels = raw6396step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6396step0 raw6396step0Labels permutation32 permutation6
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw6397 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6397step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw6397step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6397step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6397 raw6397Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw6397 raw6397Labels = mixedMoment B raw6397step0 raw6397step0Labels := by
      have hz : ∀ j, raw6397 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6397step0 = (fun i j => raw6397 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6397step0 raw6397; decide +kernel
      have hl : raw6397step0Labels = raw6397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6397 raw6397Labels permutation346 hz
    mixedMoment B raw6397step0 raw6397step0Labels = mixedMoment B raw6397step1 raw6397step1Labels := by
      have hz : ∀ j, raw6397step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6397step1 = (fun i j => raw6397step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6397step1 raw6397step0; decide +kernel
      have hl : raw6397step1Labels = raw6397step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6397step0 raw6397step0Labels permutation56 hz
    mixedMoment B raw6397step1 raw6397step1Labels = mixedMoment B raw6397step2 raw6397step2Labels := by
      have ha : raw6397step2 = (fun i j => raw6397step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6397step2 raw6397step1; decide +kernel
      have hl : raw6397step2Labels = raw6397step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6397step1 raw6397step1Labels permutation8 permutation6
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw6398 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6398step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw6398step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6398step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6398step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6398 raw6398Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw6398 raw6398Labels = mixedMoment B raw6398step0 raw6398step0Labels := by
      have hz : ∀ j, raw6398 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6398step0 = (fun i j => raw6398 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6398step0 raw6398; decide +kernel
      have hl : raw6398step0Labels = raw6398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6398 raw6398Labels permutation346 hz
    mixedMoment B raw6398step0 raw6398step0Labels = mixedMoment B raw6398step1 raw6398step1Labels := by
      have hz : ∀ j, raw6398step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw6398step1 = (fun i j => raw6398step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw6398step1 raw6398step0; decide +kernel
      have hl : raw6398step1Labels = raw6398step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6398step0 raw6398step0Labels permutation56 hz
    mixedMoment B raw6398step1 raw6398step1Labels = mixedMoment B raw6398step2 raw6398step2Labels := by
      have ha : raw6398step2 = (fun i j => raw6398step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6398step2 raw6398step1; decide +kernel
      have hl : raw6398step2Labels = raw6398step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6398step1 raw6398step1Labels permutation8 permutation6
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw6399 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6399Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6399step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6399 raw6399Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw6399 raw6399Labels = mixedMoment B raw6399step0 raw6399step0Labels := by
      have ha : raw6399step0 = (fun i j => raw6399 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6399step0 raw6399; decide +kernel
      have hl : raw6399step0Labels = raw6399Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6399 raw6399Labels permutation152 permutation6
    _ = mixedMoment B node2192 node2192Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
