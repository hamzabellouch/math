import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw14592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14592step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14592step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14592step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14592 raw14592Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw14592 raw14592Labels = mixedMoment B raw14592step0 raw14592step0Labels := by
      have ha : raw14592step0 = (fun i j => raw14592 (permutation644 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14592step0 raw14592; decide +kernel
      have hl : raw14592step0Labels = raw14592Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14592 raw14592Labels permutation644 permutation2
    mixedMoment B raw14592step0 raw14592step0Labels = mixedMoment B raw14592step1 raw14592step1Labels := by
      have ha : raw14592step1 = -raw14592step0 := by apply Matrix.ext; change ∀ i j, raw14592step1 i j = -(raw14592step0 i j); unfold raw14592step1 raw14592step0; decide +kernel
      have hl : raw14592step1Labels = raw14592step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5403 node5403Labels := by rfl

def raw14593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14593step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14593step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14593step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14593 raw14593Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw14593 raw14593Labels = mixedMoment B raw14593step0 raw14593step0Labels := by
      have ha : raw14593step0 = (fun i j => raw14593 (permutation640 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14593step0 raw14593; decide +kernel
      have hl : raw14593step0Labels = raw14593Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14593 raw14593Labels permutation640 permutation2
    mixedMoment B raw14593step0 raw14593step0Labels = mixedMoment B raw14593step1 raw14593step1Labels := by
      have ha : raw14593step1 = -raw14593step0 := by apply Matrix.ext; change ∀ i j, raw14593step1 i j = -(raw14593step0 i j); unfold raw14593step1 raw14593step0; decide +kernel
      have hl : raw14593step1Labels = raw14593step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw14594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14594step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14594step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14594step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14594 raw14594Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw14594 raw14594Labels = mixedMoment B raw14594step0 raw14594step0Labels := by
      have ha : raw14594step0 = (fun i j => raw14594 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14594step0 raw14594; decide +kernel
      have hl : raw14594step0Labels = raw14594Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14594 raw14594Labels permutation162 permutation3
    mixedMoment B raw14594step0 raw14594step0Labels = mixedMoment B raw14594step1 raw14594step1Labels := by
      have ha : raw14594step1 = raw14594step0 := by apply Matrix.ext; unfold raw14594step1 raw14594step0; decide +kernel
      have hl : raw14594step0Labels = labelEmbedding6 ∘ raw14594step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14594step0 raw14594step0Labels raw14594step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw14595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw14595step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14595step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw14595step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14595step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw14595step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14595 raw14595Labels = mixedMoment B node4785 node4785Labels := by
  calc
    mixedMoment B raw14595 raw14595Labels = mixedMoment B raw14595step0 raw14595step0Labels := by
      have ha : raw14595step0 = (fun i j => raw14595 (permutation180 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14595step0 raw14595; decide +kernel
      have hl : raw14595step0Labels = raw14595Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14595 raw14595Labels permutation180 permutation5
    mixedMoment B raw14595step0 raw14595step0Labels = mixedMoment B raw14595step1 raw14595step1Labels := by
      have ha : raw14595step1 = -raw14595step0 := by apply Matrix.ext; change ∀ i j, raw14595step1 i j = -(raw14595step0 i j); unfold raw14595step1 raw14595step0; decide +kernel
      have hl : raw14595step1Labels = raw14595step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14595step1 raw14595step1Labels = mixedMoment B raw14595step2 raw14595step2Labels := by
      have ha : raw14595step2 = raw14595step1 := by apply Matrix.ext; unfold raw14595step2 raw14595step1; decide +kernel
      have hl : raw14595step1Labels = labelEmbedding8 ∘ raw14595step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14595step1 raw14595step1Labels raw14595step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4785 node4785Labels := by rfl

def raw14596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw14596step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14596step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw14596step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14596 raw14596Labels = mixedMoment B node5347 node5347Labels := by
  calc
    mixedMoment B raw14596 raw14596Labels = mixedMoment B raw14596step0 raw14596step0Labels := by
      have ha : raw14596step0 = (fun i j => raw14596 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14596step0 raw14596; decide +kernel
      have hl : raw14596step0Labels = raw14596Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14596 raw14596Labels permutation152 permutation3
    mixedMoment B raw14596step0 raw14596step0Labels = mixedMoment B raw14596step1 raw14596step1Labels := by
      have ha : raw14596step1 = raw14596step0 := by apply Matrix.ext; unfold raw14596step1 raw14596step0; decide +kernel
      have hl : raw14596step0Labels = labelEmbedding6 ∘ raw14596step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14596step0 raw14596step0Labels raw14596step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5347 node5347Labels := by rfl

def raw14597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw14597step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14597step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw14597step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14597step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw14597step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14597 raw14597Labels = mixedMoment B node5343 node5343Labels := by
  calc
    mixedMoment B raw14597 raw14597Labels = mixedMoment B raw14597step0 raw14597step0Labels := by
      have ha : raw14597step0 = (fun i j => raw14597 (permutation180 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14597step0 raw14597; decide +kernel
      have hl : raw14597step0Labels = raw14597Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14597 raw14597Labels permutation180 permutation5
    mixedMoment B raw14597step0 raw14597step0Labels = mixedMoment B raw14597step1 raw14597step1Labels := by
      have ha : raw14597step1 = -raw14597step0 := by apply Matrix.ext; change ∀ i j, raw14597step1 i j = -(raw14597step0 i j); unfold raw14597step1 raw14597step0; decide +kernel
      have hl : raw14597step1Labels = raw14597step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14597step1 raw14597step1Labels = mixedMoment B raw14597step2 raw14597step2Labels := by
      have ha : raw14597step2 = raw14597step1 := by apply Matrix.ext; unfold raw14597step2 raw14597step1; decide +kernel
      have hl : raw14597step1Labels = labelEmbedding8 ∘ raw14597step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14597step1 raw14597step1Labels raw14597step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5343 node5343Labels := by rfl

def raw14598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14598step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14598step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14598step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14598 raw14598Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw14598 raw14598Labels = mixedMoment B raw14598step0 raw14598step0Labels := by
      have ha : raw14598step0 = (fun i j => raw14598 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14598step0 raw14598; decide +kernel
      have hl : raw14598step0Labels = raw14598Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14598 raw14598Labels permutation154 permutation3
    mixedMoment B raw14598step0 raw14598step0Labels = mixedMoment B raw14598step1 raw14598step1Labels := by
      have ha : raw14598step1 = raw14598step0 := by apply Matrix.ext; unfold raw14598step1 raw14598step0; decide +kernel
      have hl : raw14598step0Labels = labelEmbedding6 ∘ raw14598step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14598step0 raw14598step0Labels raw14598step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw14599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw14599step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14599step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw14599step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14599step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw14599step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14599 raw14599Labels = mixedMoment B node5419 node5419Labels := by
  calc
    mixedMoment B raw14599 raw14599Labels = mixedMoment B raw14599step0 raw14599step0Labels := by
      have ha : raw14599step0 = (fun i j => raw14599 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14599step0 raw14599; decide +kernel
      have hl : raw14599step0Labels = raw14599Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14599 raw14599Labels permutation194 permutation5
    mixedMoment B raw14599step0 raw14599step0Labels = mixedMoment B raw14599step1 raw14599step1Labels := by
      have ha : raw14599step1 = -raw14599step0 := by apply Matrix.ext; change ∀ i j, raw14599step1 i j = -(raw14599step0 i j); unfold raw14599step1 raw14599step0; decide +kernel
      have hl : raw14599step1Labels = raw14599step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14599step1 raw14599step1Labels = mixedMoment B raw14599step2 raw14599step2Labels := by
      have ha : raw14599step2 = raw14599step1 := by apply Matrix.ext; unfold raw14599step2 raw14599step1; decide +kernel
      have hl : raw14599step1Labels = labelEmbedding8 ∘ raw14599step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14599step1 raw14599step1Labels raw14599step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5419 node5419Labels := by rfl

def raw14600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw14600step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw14600step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14600 raw14600Labels = mixedMoment B node4781 node4781Labels := by
  calc
    mixedMoment B raw14600 raw14600Labels = mixedMoment B raw14600step0 raw14600step0Labels := by
      have ha : raw14600step0 = (fun i j => raw14600 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14600step0 raw14600; decide +kernel
      have hl : raw14600step0Labels = raw14600Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14600 raw14600Labels permutation153 permutation3
    mixedMoment B raw14600step0 raw14600step0Labels = mixedMoment B raw14600step1 raw14600step1Labels := by
      have ha : raw14600step1 = raw14600step0 := by apply Matrix.ext; unfold raw14600step1 raw14600step0; decide +kernel
      have hl : raw14600step0Labels = labelEmbedding6 ∘ raw14600step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14600step0 raw14600step0Labels raw14600step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4781 node4781Labels := by rfl

def raw14601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14601step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14601step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14601step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14601 raw14601Labels = mixedMoment B node5122 node5122Labels := by
  calc
    mixedMoment B raw14601 raw14601Labels = mixedMoment B raw14601step0 raw14601step0Labels := by
      have ha : raw14601step0 = (fun i j => raw14601 (permutation568 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14601step0 raw14601; decide +kernel
      have hl : raw14601step0Labels = raw14601Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14601 raw14601Labels permutation568 permutation5
    mixedMoment B raw14601step0 raw14601step0Labels = mixedMoment B raw14601step1 raw14601step1Labels := by
      have ha : raw14601step1 = raw14601step0 := by apply Matrix.ext; unfold raw14601step1 raw14601step0; decide +kernel
      have hl : raw14601step0Labels = labelEmbedding8 ∘ raw14601step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14601step0 raw14601step0Labels raw14601step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5122 node5122Labels := by rfl

def raw14602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw14602step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw14602step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14602 raw14602Labels = mixedMoment B node5121 node5121Labels := by
  calc
    mixedMoment B raw14602 raw14602Labels = mixedMoment B raw14602step0 raw14602step0Labels := by
      have ha : raw14602step0 = (fun i j => raw14602 (permutation566 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14602step0 raw14602; decide +kernel
      have hl : raw14602step0Labels = raw14602Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14602 raw14602Labels permutation566 permutation5
    mixedMoment B raw14602step0 raw14602step0Labels = mixedMoment B raw14602step1 raw14602step1Labels := by
      have ha : raw14602step1 = raw14602step0 := by apply Matrix.ext; unfold raw14602step1 raw14602step0; decide +kernel
      have hl : raw14602step0Labels = labelEmbedding8 ∘ raw14602step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14602step0 raw14602step0Labels raw14602step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5121 node5121Labels := by rfl

def raw14603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14603step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14603step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14603 raw14603Labels = mixedMoment B node5219 node5219Labels := by
  calc
    mixedMoment B raw14603 raw14603Labels = mixedMoment B raw14603step0 raw14603step0Labels := by
      have ha : raw14603step0 = (fun i j => raw14603 (permutation579 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14603step0 raw14603; decide +kernel
      have hl : raw14603step0Labels = raw14603Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14603 raw14603Labels permutation579 permutation5
    mixedMoment B raw14603step0 raw14603step0Labels = mixedMoment B raw14603step1 raw14603step1Labels := by
      have ha : raw14603step1 = raw14603step0 := by apply Matrix.ext; unfold raw14603step1 raw14603step0; decide +kernel
      have hl : raw14603step0Labels = labelEmbedding8 ∘ raw14603step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14603step0 raw14603step0Labels raw14603step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5219 node5219Labels := by rfl

def raw14604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![1, 1, -2]]
def raw14604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14604step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14604step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14604 raw14604Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw14604 raw14604Labels = mixedMoment B raw14604step0 raw14604step0Labels := by
      have ha : raw14604step0 = (fun i j => raw14604 (permutation559 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14604step0 raw14604; decide +kernel
      have hl : raw14604step0Labels = raw14604Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14604 raw14604Labels permutation559 permutation5
    mixedMoment B raw14604step0 raw14604step0Labels = mixedMoment B raw14604step1 raw14604step1Labels := by
      have ha : raw14604step1 = raw14604step0 := by apply Matrix.ext; unfold raw14604step1 raw14604step0; decide +kernel
      have hl : raw14604step0Labels = labelEmbedding8 ∘ raw14604step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14604step0 raw14604step0Labels raw14604step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5144 node5144Labels := by rfl

def raw14605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw14605step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw14605step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14605 raw14605Labels = mixedMoment B node4780 node4780Labels := by
  calc
    mixedMoment B raw14605 raw14605Labels = mixedMoment B raw14605step0 raw14605step0Labels := by
      have ha : raw14605step0 = (fun i j => raw14605 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14605step0 raw14605; decide +kernel
      have hl : raw14605step0Labels = raw14605Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14605 raw14605Labels permutation152 permutation3
    mixedMoment B raw14605step0 raw14605step0Labels = mixedMoment B raw14605step1 raw14605step1Labels := by
      have ha : raw14605step1 = raw14605step0 := by apply Matrix.ext; unfold raw14605step1 raw14605step0; decide +kernel
      have hl : raw14605step0Labels = labelEmbedding6 ∘ raw14605step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14605step0 raw14605step0Labels raw14605step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4780 node4780Labels := by rfl

def raw14606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw14606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw14606step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14606 raw14606Labels = mixedMoment B node5182 node5182Labels := by
  calc
    mixedMoment B raw14606 raw14606Labels = mixedMoment B raw14606step0 raw14606step0Labels := by
      have ha : raw14606step0 = (fun i j => raw14606 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14606step0 raw14606; decide +kernel
      have hl : raw14606step0Labels = raw14606Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14606 raw14606Labels permutation681 permutation2
    mixedMoment B raw14606step0 raw14606step0Labels = mixedMoment B raw14606step1 raw14606step1Labels := by
      have ha : raw14606step1 = -raw14606step0 := by apply Matrix.ext; change ∀ i j, raw14606step1 i j = -(raw14606step0 i j); unfold raw14606step1 raw14606step0; decide +kernel
      have hl : raw14606step1Labels = raw14606step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5182 node5182Labels := by rfl

def raw14607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14607step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw14607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14607 raw14607Labels = mixedMoment B node5191 node5191Labels := by
  calc
    mixedMoment B raw14607 raw14607Labels = mixedMoment B raw14607step0 raw14607step0Labels := by
      have ha : raw14607step0 = (fun i j => raw14607 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14607step0 raw14607; decide +kernel
      have hl : raw14607step0Labels = raw14607Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14607 raw14607Labels permutation688 permutation2
    mixedMoment B raw14607step0 raw14607step0Labels = mixedMoment B raw14607step1 raw14607step1Labels := by
      have ha : raw14607step1 = -raw14607step0 := by apply Matrix.ext; change ∀ i j, raw14607step1 i j = -(raw14607step0 i j); unfold raw14607step1 raw14607step0; decide +kernel
      have hl : raw14607step1Labels = raw14607step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5191 node5191Labels := by rfl

def raw14608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14608step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14608step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14608 raw14608Labels = mixedMoment B node5187 node5187Labels := by
  calc
    mixedMoment B raw14608 raw14608Labels = mixedMoment B raw14608step0 raw14608step0Labels := by
      have ha : raw14608step0 = (fun i j => raw14608 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14608step0 raw14608; decide +kernel
      have hl : raw14608step0Labels = raw14608Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14608 raw14608Labels permutation680 permutation2
    mixedMoment B raw14608step0 raw14608step0Labels = mixedMoment B raw14608step1 raw14608step1Labels := by
      have ha : raw14608step1 = -raw14608step0 := by apply Matrix.ext; change ∀ i j, raw14608step1 i j = -(raw14608step0 i j); unfold raw14608step1 raw14608step0; decide +kernel
      have hl : raw14608step1Labels = raw14608step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5187 node5187Labels := by rfl

def raw14609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw14609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14609step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14609step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14609 raw14609Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw14609 raw14609Labels = mixedMoment B raw14609step0 raw14609step0Labels := by
      have ha : raw14609step0 = (fun i j => raw14609 (permutation640 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14609step0 raw14609; decide +kernel
      have hl : raw14609step0Labels = raw14609Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14609 raw14609Labels permutation640 permutation2
    mixedMoment B raw14609step0 raw14609step0Labels = mixedMoment B raw14609step1 raw14609step1Labels := by
      have ha : raw14609step1 = -raw14609step0 := by apply Matrix.ext; change ∀ i j, raw14609step1 i j = -(raw14609step0 i j); unfold raw14609step1 raw14609step0; decide +kernel
      have hl : raw14609step1Labels = raw14609step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw14610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14610Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14610step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14610 raw14610Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw14610 raw14610Labels = mixedMoment B raw14610step0 raw14610step0Labels := by
      have ha : raw14610step0 = (fun i j => raw14610 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14610step0 raw14610; decide +kernel
      have hl : raw14610step0Labels = raw14610Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14610 raw14610Labels permutation265 permutation3
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw14611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14611Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw14611step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14611step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14611step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14611 raw14611Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw14611 raw14611Labels = mixedMoment B raw14611step0 raw14611step0Labels := by
      have ha : raw14611step0 = (fun i j => raw14611 (permutation685 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14611step0 raw14611; decide +kernel
      have hl : raw14611step0Labels = raw14611Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14611 raw14611Labels permutation685 permutation3
    mixedMoment B raw14611step0 raw14611step0Labels = mixedMoment B raw14611step1 raw14611step1Labels := by
      have ha : raw14611step1 = -raw14611step0 := by apply Matrix.ext; change ∀ i j, raw14611step1 i j = -(raw14611step0 i j); unfold raw14611step1 raw14611step0; decide +kernel
      have hl : raw14611step1Labels = raw14611step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4024 node4024Labels := by rfl

def raw14612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14612Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14612step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14612step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14612 raw14612Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw14612 raw14612Labels = mixedMoment B raw14612step0 raw14612step0Labels := by
      have ha : raw14612step0 = (fun i j => raw14612 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14612step0 raw14612; decide +kernel
      have hl : raw14612step0Labels = raw14612Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14612 raw14612Labels permutation680 permutation3
    mixedMoment B raw14612step0 raw14612step0Labels = mixedMoment B raw14612step1 raw14612step1Labels := by
      have ha : raw14612step1 = -raw14612step0 := by apply Matrix.ext; change ∀ i j, raw14612step1 i j = -(raw14612step0 i j); unfold raw14612step1 raw14612step0; decide +kernel
      have hl : raw14612step1Labels = raw14612step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4026 node4026Labels := by rfl

def raw14613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14613Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14613step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14613step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14613 raw14613Labels = mixedMoment B node4033 node4033Labels := by
  calc
    mixedMoment B raw14613 raw14613Labels = mixedMoment B raw14613step0 raw14613step0Labels := by
      have ha : raw14613step0 = (fun i j => raw14613 (permutation623 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14613step0 raw14613; decide +kernel
      have hl : raw14613step0Labels = raw14613Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14613 raw14613Labels permutation623 permutation6
    _ = mixedMoment B node4033 node4033Labels := by rfl

def raw14614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14614Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14614step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14614 raw14614Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw14614 raw14614Labels = mixedMoment B raw14614step0 raw14614step0Labels := by
      have ha : raw14614step0 = (fun i j => raw14614 (permutation623 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14614step0 raw14614; decide +kernel
      have hl : raw14614step0Labels = raw14614Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14614 raw14614Labels permutation623 permutation6
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw14615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14615Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14615step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14615 raw14615Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw14615 raw14615Labels = mixedMoment B raw14615step0 raw14615step0Labels := by
      have ha : raw14615step0 = (fun i j => raw14615 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14615step0 raw14615; decide +kernel
      have hl : raw14615step0Labels = raw14615Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14615 raw14615Labels permutation176 permutation3
    _ = mixedMoment B node2192 node2192Labels := by rfl

def raw14616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14616Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14616step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14616 raw14616Labels = mixedMoment B node3759 node3759Labels := by
  calc
    mixedMoment B raw14616 raw14616Labels = mixedMoment B raw14616step0 raw14616step0Labels := by
      have ha : raw14616step0 = (fun i j => raw14616 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14616step0 raw14616; decide +kernel
      have hl : raw14616step0Labels = raw14616Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14616 raw14616Labels permutation176 permutation3
    _ = mixedMoment B node3759 node3759Labels := by rfl

def raw14617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14617Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14617step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14617 raw14617Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw14617 raw14617Labels = mixedMoment B raw14617step0 raw14617step0Labels := by
      have ha : raw14617step0 = (fun i j => raw14617 (permutation206 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14617step0 raw14617; decide +kernel
      have hl : raw14617step0Labels = raw14617Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14617 raw14617Labels permutation206 permutation3
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw14618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14618Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw14618step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14618 raw14618Labels = mixedMoment B node3899 node3899Labels := by
  calc
    mixedMoment B raw14618 raw14618Labels = mixedMoment B raw14618step0 raw14618step0Labels := by
      have ha : raw14618step0 = (fun i j => raw14618 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14618step0 raw14618; decide +kernel
      have hl : raw14618step0Labels = raw14618Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14618 raw14618Labels permutation176 permutation3
    _ = mixedMoment B node3899 node3899Labels := by rfl

def raw14619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14619Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw14619step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14619 raw14619Labels = mixedMoment B node3900 node3900Labels := by
  calc
    mixedMoment B raw14619 raw14619Labels = mixedMoment B raw14619step0 raw14619step0Labels := by
      have ha : raw14619step0 = (fun i j => raw14619 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14619step0 raw14619; decide +kernel
      have hl : raw14619step0Labels = raw14619Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14619 raw14619Labels permutation177 permutation3
    _ = mixedMoment B node3900 node3900Labels := by rfl

def raw14620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14620Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14620step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14620 raw14620Labels = mixedMoment B node2021 node2021Labels := by
  calc
    mixedMoment B raw14620 raw14620Labels = mixedMoment B raw14620step0 raw14620step0Labels := by
      have ha : raw14620step0 = (fun i j => raw14620 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14620step0 raw14620; decide +kernel
      have hl : raw14620step0Labels = raw14620Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14620 raw14620Labels permutation158 permutation3
    _ = mixedMoment B node2021 node2021Labels := by rfl

def raw14621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14621Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14621step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14621 raw14621Labels = mixedMoment B node3691 node3691Labels := by
  calc
    mixedMoment B raw14621 raw14621Labels = mixedMoment B raw14621step0 raw14621step0Labels := by
      have ha : raw14621step0 = (fun i j => raw14621 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14621step0 raw14621; decide +kernel
      have hl : raw14621step0Labels = raw14621Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14621 raw14621Labels permutation158 permutation3
    _ = mixedMoment B node3691 node3691Labels := by rfl

def raw14622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14622Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14622step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14622 raw14622Labels = mixedMoment B node3822 node3822Labels := by
  calc
    mixedMoment B raw14622 raw14622Labels = mixedMoment B raw14622step0 raw14622step0Labels := by
      have ha : raw14622step0 = (fun i j => raw14622 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14622step0 raw14622; decide +kernel
      have hl : raw14622step0Labels = raw14622Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14622 raw14622Labels permutation158 permutation3
    _ = mixedMoment B node3822 node3822Labels := by rfl

def raw14623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14623Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw14623step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14623 raw14623Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw14623 raw14623Labels = mixedMoment B raw14623step0 raw14623step0Labels := by
      have ha : raw14623step0 = (fun i j => raw14623 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14623step0 raw14623; decide +kernel
      have hl : raw14623step0Labels = raw14623Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14623 raw14623Labels permutation160 permutation3
    _ = mixedMoment B node3847 node3847Labels := by rfl

def raw14624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14624Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14624step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14624 raw14624Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw14624 raw14624Labels = mixedMoment B raw14624step0 raw14624step0Labels := by
      have ha : raw14624step0 = (fun i j => raw14624 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14624step0 raw14624; decide +kernel
      have hl : raw14624step0Labels = raw14624Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14624 raw14624Labels permutation162 permutation3
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw14625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14625Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw14625step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14625 raw14625Labels = mixedMoment B node2002 node2002Labels := by
  calc
    mixedMoment B raw14625 raw14625Labels = mixedMoment B raw14625step0 raw14625step0Labels := by
      have ha : raw14625step0 = (fun i j => raw14625 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14625step0 raw14625; decide +kernel
      have hl : raw14625step0Labels = raw14625Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14625 raw14625Labels permutation152 permutation3
    _ = mixedMoment B node2002 node2002Labels := by rfl

def raw14626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14626Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw14626step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14626 raw14626Labels = mixedMoment B node3684 node3684Labels := by
  calc
    mixedMoment B raw14626 raw14626Labels = mixedMoment B raw14626step0 raw14626step0Labels := by
      have ha : raw14626step0 = (fun i j => raw14626 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14626step0 raw14626; decide +kernel
      have hl : raw14626step0Labels = raw14626Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14626 raw14626Labels permutation152 permutation3
    _ = mixedMoment B node3684 node3684Labels := by rfl

def raw14627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14627Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw14627step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14627 raw14627Labels = mixedMoment B node3747 node3747Labels := by
  calc
    mixedMoment B raw14627 raw14627Labels = mixedMoment B raw14627step0 raw14627step0Labels := by
      have ha : raw14627step0 = (fun i j => raw14627 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14627step0 raw14627; decide +kernel
      have hl : raw14627step0Labels = raw14627Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14627 raw14627Labels permutation176 permutation3
    _ = mixedMoment B node3747 node3747Labels := by rfl

def raw14628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14628Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14628step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14628 raw14628Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw14628 raw14628Labels = mixedMoment B raw14628step0 raw14628step0Labels := by
      have ha : raw14628step0 = (fun i j => raw14628 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14628step0 raw14628; decide +kernel
      have hl : raw14628step0Labels = raw14628Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14628 raw14628Labels permutation154 permutation3
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw14629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw14629step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14629 raw14629Labels = mixedMoment B node3842 node3842Labels := by
  calc
    mixedMoment B raw14629 raw14629Labels = mixedMoment B raw14629step0 raw14629step0Labels := by
      have ha : raw14629step0 = (fun i j => raw14629 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14629step0 raw14629; decide +kernel
      have hl : raw14629step0Labels = raw14629Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14629 raw14629Labels permutation156 permutation3
    _ = mixedMoment B node3842 node3842Labels := by rfl

def raw14630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw14630step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14630 raw14630Labels = mixedMoment B node1989 node1989Labels := by
  calc
    mixedMoment B raw14630 raw14630Labels = mixedMoment B raw14630step0 raw14630step0Labels := by
      have ha : raw14630step0 = (fun i j => raw14630 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14630step0 raw14630; decide +kernel
      have hl : raw14630step0Labels = raw14630Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14630 raw14630Labels permutation153 permutation3
    _ = mixedMoment B node1989 node1989Labels := by rfl

def raw14631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw14631step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw14631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14631 raw14631Labels = mixedMoment B node3367 node3367Labels := by
  calc
    mixedMoment B raw14631 raw14631Labels = mixedMoment B raw14631step0 raw14631step0Labels := by
      have ha : raw14631step0 = (fun i j => raw14631 (permutation589 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14631step0 raw14631; decide +kernel
      have hl : raw14631step0Labels = raw14631Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14631 raw14631Labels permutation589 permutation3
    mixedMoment B raw14631step0 raw14631step0Labels = mixedMoment B raw14631step1 raw14631step1Labels := by
      have ha : raw14631step1 = -raw14631step0 := by apply Matrix.ext; change ∀ i j, raw14631step1 i j = -(raw14631step0 i j); unfold raw14631step1 raw14631step0; decide +kernel
      have hl : raw14631step1Labels = raw14631step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3367 node3367Labels := by rfl

def raw14632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw14632step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14632 raw14632Labels = mixedMoment B node3369 node3369Labels := by
  calc
    mixedMoment B raw14632 raw14632Labels = mixedMoment B raw14632step0 raw14632step0Labels := by
      have ha : raw14632step0 = (fun i j => raw14632 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14632step0 raw14632; decide +kernel
      have hl : raw14632step0Labels = raw14632Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14632 raw14632Labels permutation587 permutation3
    mixedMoment B raw14632step0 raw14632step0Labels = mixedMoment B raw14632step1 raw14632step1Labels := by
      have ha : raw14632step1 = -raw14632step0 := by apply Matrix.ext; change ∀ i j, raw14632step1 i j = -(raw14632step0 i j); unfold raw14632step1 raw14632step0; decide +kernel
      have hl : raw14632step1Labels = raw14632step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3369 node3369Labels := by rfl

def raw14633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw14633step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14633step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14633 raw14633Labels = mixedMoment B node3375 node3375Labels := by
  calc
    mixedMoment B raw14633 raw14633Labels = mixedMoment B raw14633step0 raw14633step0Labels := by
      have ha : raw14633step0 = (fun i j => raw14633 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14633step0 raw14633; decide +kernel
      have hl : raw14633step0Labels = raw14633Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14633 raw14633Labels permutation582 permutation3
    mixedMoment B raw14633step0 raw14633step0Labels = mixedMoment B raw14633step1 raw14633step1Labels := by
      have ha : raw14633step1 = -raw14633step0 := by apply Matrix.ext; change ∀ i j, raw14633step1 i j = -(raw14633step0 i j); unfold raw14633step1 raw14633step0; decide +kernel
      have hl : raw14633step1Labels = raw14633step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3375 node3375Labels := by rfl

def raw14634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![1, 1, -2]]
def raw14634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14634step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw14634step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14634step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14634 raw14634Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw14634 raw14634Labels = mixedMoment B raw14634step0 raw14634step0Labels := by
      have ha : raw14634step0 = (fun i j => raw14634 (permutation589 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14634step0 raw14634; decide +kernel
      have hl : raw14634step0Labels = raw14634Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14634 raw14634Labels permutation589 permutation3
    mixedMoment B raw14634step0 raw14634step0Labels = mixedMoment B raw14634step1 raw14634step1Labels := by
      have ha : raw14634step1 = -raw14634step0 := by apply Matrix.ext; change ∀ i j, raw14634step1 i j = -(raw14634step0 i j); unfold raw14634step1 raw14634step0; decide +kernel
      have hl : raw14634step1Labels = raw14634step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3557 node3557Labels := by rfl

def raw14635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw14635step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14635 raw14635Labels = mixedMoment B node1988 node1988Labels := by
  calc
    mixedMoment B raw14635 raw14635Labels = mixedMoment B raw14635step0 raw14635step0Labels := by
      have ha : raw14635step0 = (fun i j => raw14635 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14635step0 raw14635; decide +kernel
      have hl : raw14635step0Labels = raw14635Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14635 raw14635Labels permutation152 permutation3
    _ = mixedMoment B node1988 node1988Labels := by rfl

def raw14636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw14636step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14636step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw14636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14636 raw14636Labels = mixedMoment B node2850 node2850Labels := by
  calc
    mixedMoment B raw14636 raw14636Labels = mixedMoment B raw14636step0 raw14636step0Labels := by
      have ha : raw14636step0 = (fun i j => raw14636 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14636step0 raw14636; decide +kernel
      have hl : raw14636step0Labels = raw14636Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14636 raw14636Labels permutation688 permutation3
    mixedMoment B raw14636step0 raw14636step0Labels = mixedMoment B raw14636step1 raw14636step1Labels := by
      have ha : raw14636step1 = -raw14636step0 := by apply Matrix.ext; change ∀ i j, raw14636step1 i j = -(raw14636step0 i j); unfold raw14636step1 raw14636step0; decide +kernel
      have hl : raw14636step1Labels = raw14636step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2850 node2850Labels := by rfl

def raw14637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14637step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw14637step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14637step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14637 raw14637Labels = mixedMoment B node2852 node2852Labels := by
  calc
    mixedMoment B raw14637 raw14637Labels = mixedMoment B raw14637step0 raw14637step0Labels := by
      have ha : raw14637step0 = (fun i j => raw14637 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14637step0 raw14637; decide +kernel
      have hl : raw14637step0Labels = raw14637Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14637 raw14637Labels permutation686 permutation3
    mixedMoment B raw14637step0 raw14637step0Labels = mixedMoment B raw14637step1 raw14637step1Labels := by
      have ha : raw14637step1 = -raw14637step0 := by apply Matrix.ext; change ∀ i j, raw14637step1 i j = -(raw14637step0 i j); unfold raw14637step1 raw14637step0; decide +kernel
      have hl : raw14637step1Labels = raw14637step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2852 node2852Labels := by rfl

def raw14638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14638Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw14638step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14638step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw14638step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14638 raw14638Labels = mixedMoment B node2861 node2861Labels := by
  calc
    mixedMoment B raw14638 raw14638Labels = mixedMoment B raw14638step0 raw14638step0Labels := by
      have ha : raw14638step0 = (fun i j => raw14638 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14638step0 raw14638; decide +kernel
      have hl : raw14638step0Labels = raw14638Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14638 raw14638Labels permutation680 permutation3
    mixedMoment B raw14638step0 raw14638step0Labels = mixedMoment B raw14638step1 raw14638step1Labels := by
      have ha : raw14638step1 = -raw14638step0 := by apply Matrix.ext; change ∀ i j, raw14638step1 i j = -(raw14638step0 i j); unfold raw14638step1 raw14638step0; decide +kernel
      have hl : raw14638step1Labels = raw14638step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2861 node2861Labels := by rfl

def raw14639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw14639Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw14639step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14639step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14639 raw14639Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw14639 raw14639Labels = mixedMoment B raw14639step0 raw14639step0Labels := by
      have ha : raw14639step0 = (fun i j => raw14639 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14639step0 raw14639; decide +kernel
      have hl : raw14639step0Labels = raw14639Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14639 raw14639Labels permutation664 permutation3
    mixedMoment B raw14639step0 raw14639step0Labels = mixedMoment B raw14639step1 raw14639step1Labels := by
      have ha : raw14639step1 = -raw14639step0 := by apply Matrix.ext; change ∀ i j, raw14639step1 i j = -(raw14639step0 i j); unfold raw14639step1 raw14639step0; decide +kernel
      have hl : raw14639step1Labels = raw14639step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3064 node3064Labels := by rfl

def raw14640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14640Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14640step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14640step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14640step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14640 raw14640Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw14640 raw14640Labels = mixedMoment B raw14640step0 raw14640step0Labels := by
      have ha : raw14640step0 = (fun i j => raw14640 (permutation628 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14640step0 raw14640; decide +kernel
      have hl : raw14640step0Labels = raw14640Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14640 raw14640Labels permutation628 permutation7
    mixedMoment B raw14640step0 raw14640step0Labels = mixedMoment B raw14640step1 raw14640step1Labels := by
      have ha : raw14640step1 = raw14640step0 := by apply Matrix.ext; unfold raw14640step1 raw14640step0; decide +kernel
      have hl : raw14640step0Labels = labelEmbedding1 ∘ raw14640step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14640step0 raw14640step0Labels raw14640step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw14641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14641Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14641step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14641step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14641step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14641 raw14641Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw14641 raw14641Labels = mixedMoment B raw14641step0 raw14641step0Labels := by
      have ha : raw14641step0 = (fun i j => raw14641 (permutation628 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14641step0 raw14641; decide +kernel
      have hl : raw14641step0Labels = raw14641Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14641 raw14641Labels permutation628 permutation7
    mixedMoment B raw14641step0 raw14641step0Labels = mixedMoment B raw14641step1 raw14641step1Labels := by
      have ha : raw14641step1 = raw14641step0 := by apply Matrix.ext; unfold raw14641step1 raw14641step0; decide +kernel
      have hl : raw14641step0Labels = labelEmbedding1 ∘ raw14641step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14641step0 raw14641step0Labels raw14641step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw14642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14642Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14642step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14642step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14642step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14642 raw14642Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw14642 raw14642Labels = mixedMoment B raw14642step0 raw14642step0Labels := by
      have ha : raw14642step0 = (fun i j => raw14642 (permutation627 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14642step0 raw14642; decide +kernel
      have hl : raw14642step0Labels = raw14642Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14642 raw14642Labels permutation627 permutation7
    mixedMoment B raw14642step0 raw14642step0Labels = mixedMoment B raw14642step1 raw14642step1Labels := by
      have ha : raw14642step1 = raw14642step0 := by apply Matrix.ext; unfold raw14642step1 raw14642step0; decide +kernel
      have hl : raw14642step0Labels = labelEmbedding1 ∘ raw14642step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14642step0 raw14642step0Labels raw14642step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3849 node3849Labels := by rfl

def raw14643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14643Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14643step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14643step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14643step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14643 raw14643Labels = mixedMoment B node3851 node3851Labels := by
  calc
    mixedMoment B raw14643 raw14643Labels = mixedMoment B raw14643step0 raw14643step0Labels := by
      have ha : raw14643step0 = (fun i j => raw14643 (permutation626 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14643step0 raw14643; decide +kernel
      have hl : raw14643step0Labels = raw14643Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14643 raw14643Labels permutation626 permutation7
    mixedMoment B raw14643step0 raw14643step0Labels = mixedMoment B raw14643step1 raw14643step1Labels := by
      have ha : raw14643step1 = raw14643step0 := by apply Matrix.ext; unfold raw14643step1 raw14643step0; decide +kernel
      have hl : raw14643step0Labels = labelEmbedding1 ∘ raw14643step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14643step0 raw14643step0Labels raw14643step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3851 node3851Labels := by rfl

def raw14644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14644Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14644step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14644step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14644 raw14644Labels = mixedMoment B node3994 node3994Labels := by
  calc
    mixedMoment B raw14644 raw14644Labels = mixedMoment B raw14644step0 raw14644step0Labels := by
      have ha : raw14644step0 = (fun i j => raw14644 (permutation559 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14644step0 raw14644; decide +kernel
      have hl : raw14644step0Labels = raw14644Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14644 raw14644Labels permutation559 permutation5
    mixedMoment B raw14644step0 raw14644step0Labels = mixedMoment B raw14644step1 raw14644step1Labels := by
      have ha : raw14644step1 = raw14644step0 := by apply Matrix.ext; unfold raw14644step1 raw14644step0; decide +kernel
      have hl : raw14644step0Labels = labelEmbedding1 ∘ raw14644step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14644step0 raw14644step0Labels raw14644step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3994 node3994Labels := by rfl

def raw14645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14645Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw14645step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14645step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14645step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14645step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14645 raw14645Labels = mixedMoment B node2033 node2033Labels := by
  calc
    mixedMoment B raw14645 raw14645Labels = mixedMoment B raw14645step0 raw14645step0Labels := by
      have ha : raw14645step0 = (fun i j => raw14645 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14645step0 raw14645; decide +kernel
      have hl : raw14645step0Labels = raw14645Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14645 raw14645Labels permutation194 permutation5
    mixedMoment B raw14645step0 raw14645step0Labels = mixedMoment B raw14645step1 raw14645step1Labels := by
      have ha : raw14645step1 = -raw14645step0 := by apply Matrix.ext; change ∀ i j, raw14645step1 i j = -(raw14645step0 i j); unfold raw14645step1 raw14645step0; decide +kernel
      have hl : raw14645step1Labels = raw14645step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14645step1 raw14645step1Labels = mixedMoment B raw14645step2 raw14645step2Labels := by
      have ha : raw14645step2 = raw14645step1 := by apply Matrix.ext; unfold raw14645step2 raw14645step1; decide +kernel
      have hl : raw14645step1Labels = labelEmbedding1 ∘ raw14645step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14645step1 raw14645step1Labels raw14645step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2033 node2033Labels := by rfl

def raw14646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14646Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14646step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw14646step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14646step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14646step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14646step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14646step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14646 raw14646Labels = mixedMoment B node3697 node3697Labels := by
  calc
    mixedMoment B raw14646 raw14646Labels = mixedMoment B raw14646step0 raw14646step0Labels := by
      have ha : raw14646step0 = (fun i j => raw14646 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14646step0 raw14646; decide +kernel
      have hl : raw14646step0Labels = raw14646Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14646 raw14646Labels permutation194 permutation5
    mixedMoment B raw14646step0 raw14646step0Labels = mixedMoment B raw14646step1 raw14646step1Labels := by
      have ha : raw14646step1 = -raw14646step0 := by apply Matrix.ext; change ∀ i j, raw14646step1 i j = -(raw14646step0 i j); unfold raw14646step1 raw14646step0; decide +kernel
      have hl : raw14646step1Labels = raw14646step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14646step1 raw14646step1Labels = mixedMoment B raw14646step2 raw14646step2Labels := by
      have ha : raw14646step2 = raw14646step1 := by apply Matrix.ext; unfold raw14646step2 raw14646step1; decide +kernel
      have hl : raw14646step1Labels = labelEmbedding1 ∘ raw14646step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14646step1 raw14646step1Labels raw14646step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3697 node3697Labels := by rfl

def raw14647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14647Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14647step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14647step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14647step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14647step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14647step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14647 raw14647Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw14647 raw14647Labels = mixedMoment B raw14647step0 raw14647step0Labels := by
      have ha : raw14647step0 = (fun i j => raw14647 (permutation186 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14647step0 raw14647; decide +kernel
      have hl : raw14647step0Labels = raw14647Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14647 raw14647Labels permutation186 permutation5
    mixedMoment B raw14647step0 raw14647step0Labels = mixedMoment B raw14647step1 raw14647step1Labels := by
      have ha : raw14647step1 = -raw14647step0 := by apply Matrix.ext; change ∀ i j, raw14647step1 i j = -(raw14647step0 i j); unfold raw14647step1 raw14647step0; decide +kernel
      have hl : raw14647step1Labels = raw14647step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14647step1 raw14647step1Labels = mixedMoment B raw14647step2 raw14647step2Labels := by
      have ha : raw14647step2 = raw14647step1 := by apply Matrix.ext; unfold raw14647step2 raw14647step1; decide +kernel
      have hl : raw14647step1Labels = labelEmbedding1 ∘ raw14647step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14647step1 raw14647step1Labels raw14647step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw14648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14648Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw14648step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14648step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14648step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14648 raw14648Labels = mixedMoment B node3855 node3855Labels := by
  calc
    mixedMoment B raw14648 raw14648Labels = mixedMoment B raw14648step0 raw14648step0Labels := by
      have ha : raw14648step0 = (fun i j => raw14648 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14648step0 raw14648; decide +kernel
      have hl : raw14648step0Labels = raw14648Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14648 raw14648Labels permutation194 permutation5
    mixedMoment B raw14648step0 raw14648step0Labels = mixedMoment B raw14648step1 raw14648step1Labels := by
      have ha : raw14648step1 = -raw14648step0 := by apply Matrix.ext; change ∀ i j, raw14648step1 i j = -(raw14648step0 i j); unfold raw14648step1 raw14648step0; decide +kernel
      have hl : raw14648step1Labels = raw14648step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14648step1 raw14648step1Labels = mixedMoment B raw14648step2 raw14648step2Labels := by
      have ha : raw14648step2 = raw14648step1 := by apply Matrix.ext; unfold raw14648step2 raw14648step1; decide +kernel
      have hl : raw14648step1Labels = labelEmbedding1 ∘ raw14648step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14648step1 raw14648step1Labels raw14648step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3855 node3855Labels := by rfl

def raw14649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14649Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw14649step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14649step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14649step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14649step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw14649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14649 raw14649Labels = mixedMoment B node3829 node3829Labels := by
  calc
    mixedMoment B raw14649 raw14649Labels = mixedMoment B raw14649step0 raw14649step0Labels := by
      have ha : raw14649step0 = (fun i j => raw14649 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14649step0 raw14649; decide +kernel
      have hl : raw14649step0Labels = raw14649Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14649 raw14649Labels permutation194 permutation5
    mixedMoment B raw14649step0 raw14649step0Labels = mixedMoment B raw14649step1 raw14649step1Labels := by
      have ha : raw14649step1 = -raw14649step0 := by apply Matrix.ext; change ∀ i j, raw14649step1 i j = -(raw14649step0 i j); unfold raw14649step1 raw14649step0; decide +kernel
      have hl : raw14649step1Labels = raw14649step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14649step1 raw14649step1Labels = mixedMoment B raw14649step2 raw14649step2Labels := by
      have ha : raw14649step2 = raw14649step1 := by apply Matrix.ext; unfold raw14649step2 raw14649step1; decide +kernel
      have hl : raw14649step1Labels = labelEmbedding1 ∘ raw14649step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14649step1 raw14649step1Labels raw14649step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3829 node3829Labels := by rfl

def raw14650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14650Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14650step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14650step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14650step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14650step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14650step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14650 raw14650Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw14650 raw14650Labels = mixedMoment B raw14650step0 raw14650step0Labels := by
      have ha : raw14650step0 = (fun i j => raw14650 (permutation156 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14650step0 raw14650; decide +kernel
      have hl : raw14650step0Labels = raw14650Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14650 raw14650Labels permutation156 permutation5
    mixedMoment B raw14650step0 raw14650step0Labels = mixedMoment B raw14650step1 raw14650step1Labels := by
      have ha : raw14650step1 = -raw14650step0 := by apply Matrix.ext; change ∀ i j, raw14650step1 i j = -(raw14650step0 i j); unfold raw14650step1 raw14650step0; decide +kernel
      have hl : raw14650step1Labels = raw14650step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14650step1 raw14650step1Labels = mixedMoment B raw14650step2 raw14650step2Labels := by
      have ha : raw14650step2 = raw14650step1 := by apply Matrix.ext; unfold raw14650step2 raw14650step1; decide +kernel
      have hl : raw14650step1Labels = labelEmbedding1 ∘ raw14650step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14650step1 raw14650step1Labels raw14650step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw14651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14651Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14651step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14651step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14651step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14651step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14651step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14651 raw14651Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw14651 raw14651Labels = mixedMoment B raw14651step0 raw14651step0Labels := by
      have ha : raw14651step0 = (fun i j => raw14651 (permutation156 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14651step0 raw14651; decide +kernel
      have hl : raw14651step0Labels = raw14651Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14651 raw14651Labels permutation156 permutation5
    mixedMoment B raw14651step0 raw14651step0Labels = mixedMoment B raw14651step1 raw14651step1Labels := by
      have ha : raw14651step1 = -raw14651step0 := by apply Matrix.ext; change ∀ i j, raw14651step1 i j = -(raw14651step0 i j); unfold raw14651step1 raw14651step0; decide +kernel
      have hl : raw14651step1Labels = raw14651step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14651step1 raw14651step1Labels = mixedMoment B raw14651step2 raw14651step2Labels := by
      have ha : raw14651step2 = raw14651step1 := by apply Matrix.ext; unfold raw14651step2 raw14651step1; decide +kernel
      have hl : raw14651step1Labels = labelEmbedding1 ∘ raw14651step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14651step1 raw14651step1Labels raw14651step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw14652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14652Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14652step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14652 raw14652Labels = mixedMoment B node3810 node3810Labels := by
  calc
    mixedMoment B raw14652 raw14652Labels = mixedMoment B raw14652step0 raw14652step0Labels := by
      have ha : raw14652step0 = (fun i j => raw14652 (permutation627 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14652step0 raw14652; decide +kernel
      have hl : raw14652step0Labels = raw14652Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14652 raw14652Labels permutation627 permutation7
    mixedMoment B raw14652step0 raw14652step0Labels = mixedMoment B raw14652step1 raw14652step1Labels := by
      have ha : raw14652step1 = raw14652step0 := by apply Matrix.ext; unfold raw14652step1 raw14652step0; decide +kernel
      have hl : raw14652step0Labels = labelEmbedding1 ∘ raw14652step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14652step0 raw14652step0Labels raw14652step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3810 node3810Labels := by rfl

def raw14653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14653Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14653step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14653 raw14653Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw14653 raw14653Labels = mixedMoment B raw14653step0 raw14653step0Labels := by
      have ha : raw14653step0 = (fun i j => raw14653 (permutation626 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14653step0 raw14653; decide +kernel
      have hl : raw14653step0Labels = raw14653Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14653 raw14653Labels permutation626 permutation7
    mixedMoment B raw14653step0 raw14653step0Labels = mixedMoment B raw14653step1 raw14653step1Labels := by
      have ha : raw14653step1 = raw14653step0 := by apply Matrix.ext; unfold raw14653step1 raw14653step0; decide +kernel
      have hl : raw14653step0Labels = labelEmbedding1 ∘ raw14653step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14653step0 raw14653step0Labels raw14653step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3812 node3812Labels := by rfl

def raw14654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14654Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14654step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14654step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14654step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14654step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14654step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14654 raw14654Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw14654 raw14654Labels = mixedMoment B raw14654step0 raw14654step0Labels := by
      have ha : raw14654step0 = (fun i j => raw14654 (permutation246 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14654step0 raw14654; decide +kernel
      have hl : raw14654step0Labels = raw14654Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14654 raw14654Labels permutation246 permutation5
    mixedMoment B raw14654step0 raw14654step0Labels = mixedMoment B raw14654step1 raw14654step1Labels := by
      have ha : raw14654step1 = -raw14654step0 := by apply Matrix.ext; change ∀ i j, raw14654step1 i j = -(raw14654step0 i j); unfold raw14654step1 raw14654step0; decide +kernel
      have hl : raw14654step1Labels = raw14654step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14654step1 raw14654step1Labels = mixedMoment B raw14654step2 raw14654step2Labels := by
      have ha : raw14654step2 = raw14654step1 := by apply Matrix.ext; unfold raw14654step2 raw14654step1; decide +kernel
      have hl : raw14654step1Labels = labelEmbedding1 ∘ raw14654step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14654step1 raw14654step1Labels raw14654step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw14655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14655Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw14655step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw14655step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14655step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw14655step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14655 raw14655Labels = mixedMoment B node1994 node1994Labels := by
  calc
    mixedMoment B raw14655 raw14655Labels = mixedMoment B raw14655step0 raw14655step0Labels := by
      have ha : raw14655step0 = (fun i j => raw14655 (permutation180 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14655step0 raw14655; decide +kernel
      have hl : raw14655step0Labels = raw14655Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14655 raw14655Labels permutation180 permutation5
    mixedMoment B raw14655step0 raw14655step0Labels = mixedMoment B raw14655step1 raw14655step1Labels := by
      have ha : raw14655step1 = -raw14655step0 := by apply Matrix.ext; change ∀ i j, raw14655step1 i j = -(raw14655step0 i j); unfold raw14655step1 raw14655step0; decide +kernel
      have hl : raw14655step1Labels = raw14655step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14655step1 raw14655step1Labels = mixedMoment B raw14655step2 raw14655step2Labels := by
      have ha : raw14655step2 = raw14655step1 := by apply Matrix.ext; unfold raw14655step2 raw14655step1; decide +kernel
      have hl : raw14655step1Labels = labelEmbedding1 ∘ raw14655step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14655step1 raw14655step1Labels raw14655step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1994 node1994Labels := by rfl

def raw14656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14656Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -1, 0], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw14656step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw14656step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14656step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw14656step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14656 raw14656Labels = mixedMoment B node3743 node3743Labels := by
  calc
    mixedMoment B raw14656 raw14656Labels = mixedMoment B raw14656step0 raw14656step0Labels := by
      have ha : raw14656step0 = (fun i j => raw14656 (permutation156 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14656step0 raw14656; decide +kernel
      have hl : raw14656step0Labels = raw14656Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14656 raw14656Labels permutation156 permutation5
    mixedMoment B raw14656step0 raw14656step0Labels = mixedMoment B raw14656step1 raw14656step1Labels := by
      have ha : raw14656step1 = -raw14656step0 := by apply Matrix.ext; change ∀ i j, raw14656step1 i j = -(raw14656step0 i j); unfold raw14656step1 raw14656step0; decide +kernel
      have hl : raw14656step1Labels = raw14656step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14656step1 raw14656step1Labels = mixedMoment B raw14656step2 raw14656step2Labels := by
      have ha : raw14656step2 = raw14656step1 := by apply Matrix.ext; unfold raw14656step2 raw14656step1; decide +kernel
      have hl : raw14656step1Labels = labelEmbedding1 ∘ raw14656step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14656step1 raw14656step1Labels raw14656step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3743 node3743Labels := by rfl

def raw14657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14657Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14657step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw14657step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14657step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw14657step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14657step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw14657step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14657 raw14657Labels = mixedMoment B node3680 node3680Labels := by
  calc
    mixedMoment B raw14657 raw14657Labels = mixedMoment B raw14657step0 raw14657step0Labels := by
      have ha : raw14657step0 = (fun i j => raw14657 (permutation180 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14657step0 raw14657; decide +kernel
      have hl : raw14657step0Labels = raw14657Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14657 raw14657Labels permutation180 permutation5
    mixedMoment B raw14657step0 raw14657step0Labels = mixedMoment B raw14657step1 raw14657step1Labels := by
      have ha : raw14657step1 = -raw14657step0 := by apply Matrix.ext; change ∀ i j, raw14657step1 i j = -(raw14657step0 i j); unfold raw14657step1 raw14657step0; decide +kernel
      have hl : raw14657step1Labels = raw14657step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14657step1 raw14657step1Labels = mixedMoment B raw14657step2 raw14657step2Labels := by
      have ha : raw14657step2 = raw14657step1 := by apply Matrix.ext; unfold raw14657step2 raw14657step1; decide +kernel
      have hl : raw14657step1Labels = labelEmbedding1 ∘ raw14657step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14657step1 raw14657step1Labels raw14657step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3680 node3680Labels := by rfl

def raw14658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14658Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14658step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14658step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14658step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14658step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14658step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14658 raw14658Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw14658 raw14658Labels = mixedMoment B raw14658step0 raw14658step0Labels := by
      have ha : raw14658step0 = (fun i j => raw14658 (permutation181 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14658step0 raw14658; decide +kernel
      have hl : raw14658step0Labels = raw14658Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14658 raw14658Labels permutation181 permutation5
    mixedMoment B raw14658step0 raw14658step0Labels = mixedMoment B raw14658step1 raw14658step1Labels := by
      have ha : raw14658step1 = -raw14658step0 := by apply Matrix.ext; change ∀ i j, raw14658step1 i j = -(raw14658step0 i j); unfold raw14658step1 raw14658step0; decide +kernel
      have hl : raw14658step1Labels = raw14658step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14658step1 raw14658step1Labels = mixedMoment B raw14658step2 raw14658step2Labels := by
      have ha : raw14658step2 = raw14658step1 := by apply Matrix.ext; unfold raw14658step2 raw14658step1; decide +kernel
      have hl : raw14658step1Labels = labelEmbedding1 ∘ raw14658step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14658step1 raw14658step1Labels raw14658step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw14659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14659Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw14659step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14659step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw14659step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14659step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw14659step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14659 raw14659Labels = mixedMoment B node3825 node3825Labels := by
  calc
    mixedMoment B raw14659 raw14659Labels = mixedMoment B raw14659step0 raw14659step0Labels := by
      have ha : raw14659step0 = (fun i j => raw14659 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14659step0 raw14659; decide +kernel
      have hl : raw14659step0Labels = raw14659Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14659 raw14659Labels permutation194 permutation5
    mixedMoment B raw14659step0 raw14659step0Labels = mixedMoment B raw14659step1 raw14659step1Labels := by
      have ha : raw14659step1 = -raw14659step0 := by apply Matrix.ext; change ∀ i j, raw14659step1 i j = -(raw14659step0 i j); unfold raw14659step1 raw14659step0; decide +kernel
      have hl : raw14659step1Labels = raw14659step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14659step1 raw14659step1Labels = mixedMoment B raw14659step2 raw14659step2Labels := by
      have ha : raw14659step2 = raw14659step1 := by apply Matrix.ext; unfold raw14659step2 raw14659step1; decide +kernel
      have hl : raw14659step1Labels = labelEmbedding1 ∘ raw14659step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14659step1 raw14659step1Labels raw14659step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3825 node3825Labels := by rfl

def raw14660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14660Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14660step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw14660step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14660step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw14660step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14660step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw14660step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14660 raw14660Labels = mixedMoment B node1991 node1991Labels := by
  calc
    mixedMoment B raw14660 raw14660Labels = mixedMoment B raw14660step0 raw14660step0Labels := by
      have ha : raw14660step0 = (fun i j => raw14660 (permutation180 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14660step0 raw14660; decide +kernel
      have hl : raw14660step0Labels = raw14660Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14660 raw14660Labels permutation180 permutation5
    mixedMoment B raw14660step0 raw14660step0Labels = mixedMoment B raw14660step1 raw14660step1Labels := by
      have ha : raw14660step1 = -raw14660step0 := by apply Matrix.ext; change ∀ i j, raw14660step1 i j = -(raw14660step0 i j); unfold raw14660step1 raw14660step0; decide +kernel
      have hl : raw14660step1Labels = raw14660step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14660step1 raw14660step1Labels = mixedMoment B raw14660step2 raw14660step2Labels := by
      have ha : raw14660step2 = raw14660step1 := by apply Matrix.ext; unfold raw14660step2 raw14660step1; decide +kernel
      have hl : raw14660step1Labels = labelEmbedding1 ∘ raw14660step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14660step1 raw14660step1Labels raw14660step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1991 node1991Labels := by rfl

def raw14661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14661Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14661step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14661step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14661step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw14661step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14661 raw14661Labels = mixedMoment B node2535 node2535Labels := by
  calc
    mixedMoment B raw14661 raw14661Labels = mixedMoment B raw14661step0 raw14661step0Labels := by
      have ha : raw14661step0 = (fun i j => raw14661 (permutation568 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14661step0 raw14661; decide +kernel
      have hl : raw14661step0Labels = raw14661Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14661 raw14661Labels permutation568 permutation5
    mixedMoment B raw14661step0 raw14661step0Labels = mixedMoment B raw14661step1 raw14661step1Labels := by
      have ha : raw14661step1 = raw14661step0 := by apply Matrix.ext; unfold raw14661step1 raw14661step0; decide +kernel
      have hl : raw14661step0Labels = labelEmbedding1 ∘ raw14661step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14661step0 raw14661step0Labels raw14661step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2535 node2535Labels := by rfl

def raw14662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14662Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw14662step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14662step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw14662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14662 raw14662Labels = mixedMoment B node2533 node2533Labels := by
  calc
    mixedMoment B raw14662 raw14662Labels = mixedMoment B raw14662step0 raw14662step0Labels := by
      have ha : raw14662step0 = (fun i j => raw14662 (permutation566 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14662step0 raw14662; decide +kernel
      have hl : raw14662step0Labels = raw14662Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14662 raw14662Labels permutation566 permutation5
    mixedMoment B raw14662step0 raw14662step0Labels = mixedMoment B raw14662step1 raw14662step1Labels := by
      have ha : raw14662step1 = raw14662step0 := by apply Matrix.ext; unfold raw14662step1 raw14662step0; decide +kernel
      have hl : raw14662step0Labels = labelEmbedding1 ∘ raw14662step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14662step0 raw14662step0Labels raw14662step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2533 node2533Labels := by rfl

def raw14663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14663Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14663step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14663step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14663step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw14663step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14663 raw14663Labels = mixedMoment B node2661 node2661Labels := by
  calc
    mixedMoment B raw14663 raw14663Labels = mixedMoment B raw14663step0 raw14663step0Labels := by
      have ha : raw14663step0 = (fun i j => raw14663 (permutation579 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14663step0 raw14663; decide +kernel
      have hl : raw14663step0Labels = raw14663Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14663 raw14663Labels permutation579 permutation5
    mixedMoment B raw14663step0 raw14663step0Labels = mixedMoment B raw14663step1 raw14663step1Labels := by
      have ha : raw14663step1 = raw14663step0 := by apply Matrix.ext; unfold raw14663step1 raw14663step0; decide +kernel
      have hl : raw14663step0Labels = labelEmbedding1 ∘ raw14663step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14663step0 raw14663step0Labels raw14663step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2661 node2661Labels := by rfl

def raw14664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![1, 1, -2]]
def raw14664Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14664step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14664step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14664step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14664step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14664 raw14664Labels = mixedMoment B node2566 node2566Labels := by
  calc
    mixedMoment B raw14664 raw14664Labels = mixedMoment B raw14664step0 raw14664step0Labels := by
      have ha : raw14664step0 = (fun i j => raw14664 (permutation559 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14664step0 raw14664; decide +kernel
      have hl : raw14664step0Labels = raw14664Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14664 raw14664Labels permutation559 permutation5
    mixedMoment B raw14664step0 raw14664step0Labels = mixedMoment B raw14664step1 raw14664step1Labels := by
      have ha : raw14664step1 = raw14664step0 := by apply Matrix.ext; unfold raw14664step1 raw14664step0; decide +kernel
      have hl : raw14664step0Labels = labelEmbedding1 ∘ raw14664step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14664step0 raw14664step0Labels raw14664step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2566 node2566Labels := by rfl

def raw14665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14665Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14665step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw14665step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14665step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw14665step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14665step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw14665step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14665 raw14665Labels = mixedMoment B node1998 node1998Labels := by
  calc
    mixedMoment B raw14665 raw14665Labels = mixedMoment B raw14665step0 raw14665step0Labels := by
      have ha : raw14665step0 = (fun i j => raw14665 (permutation177 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14665step0 raw14665; decide +kernel
      have hl : raw14665step0Labels = raw14665Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14665 raw14665Labels permutation177 permutation5
    mixedMoment B raw14665step0 raw14665step0Labels = mixedMoment B raw14665step1 raw14665step1Labels := by
      have ha : raw14665step1 = -raw14665step0 := by apply Matrix.ext; change ∀ i j, raw14665step1 i j = -(raw14665step0 i j); unfold raw14665step1 raw14665step0; decide +kernel
      have hl : raw14665step1Labels = raw14665step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14665step1 raw14665step1Labels = mixedMoment B raw14665step2 raw14665step2Labels := by
      have ha : raw14665step2 = raw14665step1 := by apply Matrix.ext; unfold raw14665step2 raw14665step1; decide +kernel
      have hl : raw14665step1Labels = labelEmbedding1 ∘ raw14665step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14665step1 raw14665step1Labels raw14665step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1998 node1998Labels := by rfl

def raw14666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14666Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14666step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14666step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14666step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14666 raw14666Labels = mixedMoment B node3536 node3536Labels := by
  calc
    mixedMoment B raw14666 raw14666Labels = mixedMoment B raw14666step0 raw14666step0Labels := by
      have ha : raw14666step0 = (fun i j => raw14666 (permutation628 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14666step0 raw14666; decide +kernel
      have hl : raw14666step0Labels = raw14666Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14666 raw14666Labels permutation628 permutation7
    mixedMoment B raw14666step0 raw14666step0Labels = mixedMoment B raw14666step1 raw14666step1Labels := by
      have ha : raw14666step1 = raw14666step0 := by apply Matrix.ext; unfold raw14666step1 raw14666step0; decide +kernel
      have hl : raw14666step0Labels = labelEmbedding1 ∘ raw14666step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14666step0 raw14666step0Labels raw14666step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3536 node3536Labels := by rfl

def raw14667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14667Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14667step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14667step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14667step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14667step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14667 raw14667Labels = mixedMoment B node3574 node3574Labels := by
  calc
    mixedMoment B raw14667 raw14667Labels = mixedMoment B raw14667step0 raw14667step0Labels := by
      have ha : raw14667step0 = (fun i j => raw14667 (permutation628 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14667step0 raw14667; decide +kernel
      have hl : raw14667step0Labels = raw14667Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14667 raw14667Labels permutation628 permutation7
    mixedMoment B raw14667step0 raw14667step0Labels = mixedMoment B raw14667step1 raw14667step1Labels := by
      have ha : raw14667step1 = raw14667step0 := by apply Matrix.ext; unfold raw14667step1 raw14667step0; decide +kernel
      have hl : raw14667step0Labels = labelEmbedding1 ∘ raw14667step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14667step0 raw14667step0Labels raw14667step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3574 node3574Labels := by rfl

def raw14668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14668Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14668step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14668step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14668step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw14668step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14668 raw14668Labels = mixedMoment B node3537 node3537Labels := by
  calc
    mixedMoment B raw14668 raw14668Labels = mixedMoment B raw14668step0 raw14668step0Labels := by
      have ha : raw14668step0 = (fun i j => raw14668 (permutation627 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14668step0 raw14668; decide +kernel
      have hl : raw14668step0Labels = raw14668Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14668 raw14668Labels permutation627 permutation7
    mixedMoment B raw14668step0 raw14668step0Labels = mixedMoment B raw14668step1 raw14668step1Labels := by
      have ha : raw14668step1 = raw14668step0 := by apply Matrix.ext; unfold raw14668step1 raw14668step0; decide +kernel
      have hl : raw14668step0Labels = labelEmbedding1 ∘ raw14668step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14668step0 raw14668step0Labels raw14668step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3537 node3537Labels := by rfl

def raw14669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, -1, -2]]
def raw14669Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw14669step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14669step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw14669step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14669step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14669 raw14669Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw14669 raw14669Labels = mixedMoment B raw14669step0 raw14669step0Labels := by
      have ha : raw14669step0 = (fun i j => raw14669 (permutation626 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14669step0 raw14669; decide +kernel
      have hl : raw14669step0Labels = raw14669Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14669 raw14669Labels permutation626 permutation7
    mixedMoment B raw14669step0 raw14669step0Labels = mixedMoment B raw14669step1 raw14669step1Labels := by
      have ha : raw14669step1 = raw14669step0 := by apply Matrix.ext; unfold raw14669step1 raw14669step0; decide +kernel
      have hl : raw14669step0Labels = labelEmbedding1 ∘ raw14669step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14669step0 raw14669step0Labels raw14669step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

def raw14670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14670Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14670step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14670step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14670step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14670step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14670 raw14670Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw14670 raw14670Labels = mixedMoment B raw14670step0 raw14670step0Labels := by
      have ha : raw14670step0 = (fun i j => raw14670 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14670step0 raw14670; decide +kernel
      have hl : raw14670step0Labels = raw14670Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14670 raw14670Labels permutation682 permutation2
    mixedMoment B raw14670step0 raw14670step0Labels = mixedMoment B raw14670step1 raw14670step1Labels := by
      have ha : raw14670step1 = -raw14670step0 := by apply Matrix.ext; change ∀ i j, raw14670step1 i j = -(raw14670step0 i j); unfold raw14670step1 raw14670step0; decide +kernel
      have hl : raw14670step1Labels = raw14670step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw14671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14671Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14671step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14671step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14671step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14671step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14671 raw14671Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw14671 raw14671Labels = mixedMoment B raw14671step0 raw14671step0Labels := by
      have ha : raw14671step0 = (fun i j => raw14671 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14671step0 raw14671; decide +kernel
      have hl : raw14671step0Labels = raw14671Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14671 raw14671Labels permutation681 permutation2
    mixedMoment B raw14671step0 raw14671step0Labels = mixedMoment B raw14671step1 raw14671step1Labels := by
      have ha : raw14671step1 = -raw14671step0 := by apply Matrix.ext; change ∀ i j, raw14671step1 i j = -(raw14671step0 i j); unfold raw14671step1 raw14671step0; decide +kernel
      have hl : raw14671step1Labels = raw14671step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw14672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14672Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14672step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14672step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14672 raw14672Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw14672 raw14672Labels = mixedMoment B raw14672step0 raw14672step0Labels := by
      have ha : raw14672step0 = (fun i j => raw14672 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14672step0 raw14672; decide +kernel
      have hl : raw14672step0Labels = raw14672Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14672 raw14672Labels permutation687 permutation2
    mixedMoment B raw14672step0 raw14672step0Labels = mixedMoment B raw14672step1 raw14672step1Labels := by
      have ha : raw14672step1 = -raw14672step0 := by apply Matrix.ext; change ∀ i j, raw14672step1 i j = -(raw14672step0 i j); unfold raw14672step1 raw14672step0; decide +kernel
      have hl : raw14672step1Labels = raw14672step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw14673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14673Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14673step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw14673step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14673step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14673step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14673 raw14673Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw14673 raw14673Labels = mixedMoment B raw14673step0 raw14673step0Labels := by
      have ha : raw14673step0 = (fun i j => raw14673 (permutation677 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14673step0 raw14673; decide +kernel
      have hl : raw14673step0Labels = raw14673Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14673 raw14673Labels permutation677 permutation2
    mixedMoment B raw14673step0 raw14673step0Labels = mixedMoment B raw14673step1 raw14673step1Labels := by
      have ha : raw14673step1 = -raw14673step0 := by apply Matrix.ext; change ∀ i j, raw14673step1 i j = -(raw14673step0 i j); unfold raw14673step1 raw14673step0; decide +kernel
      have hl : raw14673step1Labels = raw14673step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw14674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14674Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14674step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14674step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14674step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw14674step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14674 raw14674Labels = mixedMoment B node3901 node3901Labels := by
  calc
    mixedMoment B raw14674 raw14674Labels = mixedMoment B raw14674step0 raw14674step0Labels := by
      have ha : raw14674step0 = (fun i j => raw14674 (permutation639 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14674step0 raw14674; decide +kernel
      have hl : raw14674step0Labels = raw14674Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14674 raw14674Labels permutation639 permutation2
    mixedMoment B raw14674step0 raw14674step0Labels = mixedMoment B raw14674step1 raw14674step1Labels := by
      have ha : raw14674step1 = -raw14674step0 := by apply Matrix.ext; change ∀ i j, raw14674step1 i j = -(raw14674step0 i j); unfold raw14674step1 raw14674step0; decide +kernel
      have hl : raw14674step1Labels = raw14674step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3901 node3901Labels := by rfl

def raw14675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14675Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14675step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14675step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14675 raw14675Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw14675 raw14675Labels = mixedMoment B raw14675step0 raw14675step0Labels := by
      have ha : raw14675step0 = (fun i j => raw14675 (permutation554 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14675step0 raw14675; decide +kernel
      have hl : raw14675step0Labels = raw14675Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14675 raw14675Labels permutation554 permutation4
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw14676 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![2, -2]]
def raw14676Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14676step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-1, 1], ![-1, 1], ![2, -2]]
def raw14676step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14676step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw14676step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14676step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw14676step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14676 raw14676Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw14676 raw14676Labels = mixedMoment B raw14676step0 raw14676step0Labels := by
      have hz : ∀ j, raw14676 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw14676step0 = (fun i j => raw14676 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw14676step0 raw14676; decide +kernel
      have hl : raw14676step0Labels = raw14676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14676 raw14676Labels permutation152 hz
    mixedMoment B raw14676step0 raw14676step0Labels = mixedMoment B raw14676step1 raw14676step1Labels := by
      have ha : raw14676step1 = (fun i j => raw14676step0 (permutation134 i) (permutation0 j)) := by apply Matrix.ext; unfold raw14676step1 raw14676step0; decide +kernel
      have hl : raw14676step1Labels = raw14676step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14676step0 raw14676step0Labels permutation134 permutation0
    mixedMoment B raw14676step1 raw14676step1Labels = mixedMoment B raw14676step2 raw14676step2Labels := by
      have ha : raw14676step2 = -raw14676step1 := by apply Matrix.ext; change ∀ i j, raw14676step2 i j = -(raw14676step1 i j); unfold raw14676step2 raw14676step1; decide +kernel
      have hl : raw14676step2Labels = raw14676step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw14677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14677Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14677step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14677step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14677step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14677step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14677 raw14677Labels = mixedMoment B node3197 node3197Labels := by
  calc
    mixedMoment B raw14677 raw14677Labels = mixedMoment B raw14677step0 raw14677step0Labels := by
      have ha : raw14677step0 = (fun i j => raw14677 (permutation194 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14677step0 raw14677; decide +kernel
      have hl : raw14677step0Labels = raw14677Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14677 raw14677Labels permutation194 permutation4
    mixedMoment B raw14677step0 raw14677step0Labels = mixedMoment B raw14677step1 raw14677step1Labels := by
      have ha : raw14677step1 = -raw14677step0 := by apply Matrix.ext; change ∀ i j, raw14677step1 i j = -(raw14677step0 i j); unfold raw14677step1 raw14677step0; decide +kernel
      have hl : raw14677step1Labels = raw14677step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3197 node3197Labels := by rfl

def raw14678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14678Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14678step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw14678step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14678 raw14678Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw14678 raw14678Labels = mixedMoment B raw14678step0 raw14678step0Labels := by
      have ha : raw14678step0 = (fun i j => raw14678 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14678step0 raw14678; decide +kernel
      have hl : raw14678step0Labels = raw14678Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14678 raw14678Labels permutation160 permutation2
    _ = mixedMoment B node3202 node3202Labels := by rfl

def raw14679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14679Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14679step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, 0, -1], ![0, 2, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw14679step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14679step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw14679step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14679 raw14679Labels = mixedMoment B node3195 node3195Labels := by
  calc
    mixedMoment B raw14679 raw14679Labels = mixedMoment B raw14679step0 raw14679step0Labels := by
      have ha : raw14679step0 = (fun i j => raw14679 (permutation194 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14679step0 raw14679; decide +kernel
      have hl : raw14679step0Labels = raw14679Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14679 raw14679Labels permutation194 permutation4
    mixedMoment B raw14679step0 raw14679step0Labels = mixedMoment B raw14679step1 raw14679step1Labels := by
      have ha : raw14679step1 = -raw14679step0 := by apply Matrix.ext; change ∀ i j, raw14679step1 i j = -(raw14679step0 i j); unfold raw14679step1 raw14679step0; decide +kernel
      have hl : raw14679step1Labels = raw14679step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3195 node3195Labels := by rfl

def raw14680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14680Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14680step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw14680step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14680 raw14680Labels = mixedMoment B node2919 node2919Labels := by
  calc
    mixedMoment B raw14680 raw14680Labels = mixedMoment B raw14680step0 raw14680step0Labels := by
      have ha : raw14680step0 = (fun i j => raw14680 (permutation559 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14680step0 raw14680; decide +kernel
      have hl : raw14680step0Labels = raw14680Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14680 raw14680Labels permutation559 permutation4
    _ = mixedMoment B node2919 node2919Labels := by rfl

def raw14681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14681Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw14681step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14681step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw14681step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14681 raw14681Labels = mixedMoment B node2611 node2611Labels := by
  calc
    mixedMoment B raw14681 raw14681Labels = mixedMoment B raw14681step0 raw14681step0Labels := by
      have ha : raw14681step0 = (fun i j => raw14681 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14681step0 raw14681; decide +kernel
      have hl : raw14681step0Labels = raw14681Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14681 raw14681Labels permutation682 permutation2
    mixedMoment B raw14681step0 raw14681step0Labels = mixedMoment B raw14681step1 raw14681step1Labels := by
      have ha : raw14681step1 = -raw14681step0 := by apply Matrix.ext; change ∀ i j, raw14681step1 i j = -(raw14681step0 i j); unfold raw14681step1 raw14681step0; decide +kernel
      have hl : raw14681step1Labels = raw14681step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2611 node2611Labels := by rfl

def raw14682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14682Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14682step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 2, 0]]
def raw14682step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14682step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw14682step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14682 raw14682Labels = mixedMoment B node3878 node3878Labels := by
  calc
    mixedMoment B raw14682 raw14682Labels = mixedMoment B raw14682step0 raw14682step0Labels := by
      have ha : raw14682step0 = (fun i j => raw14682 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14682step0 raw14682; decide +kernel
      have hl : raw14682step0Labels = raw14682Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14682 raw14682Labels permutation676 permutation2
    mixedMoment B raw14682step0 raw14682step0Labels = mixedMoment B raw14682step1 raw14682step1Labels := by
      have ha : raw14682step1 = -raw14682step0 := by apply Matrix.ext; change ∀ i j, raw14682step1 i j = -(raw14682step0 i j); unfold raw14682step1 raw14682step0; decide +kernel
      have hl : raw14682step1Labels = raw14682step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3878 node3878Labels := by rfl

def raw14683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14683Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14683step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14683step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14683step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14683 raw14683Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw14683 raw14683Labels = mixedMoment B raw14683step0 raw14683step0Labels := by
      have ha : raw14683step0 = (fun i j => raw14683 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14683step0 raw14683; decide +kernel
      have hl : raw14683step0Labels = raw14683Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14683 raw14683Labels permutation680 permutation2
    mixedMoment B raw14683step0 raw14683step0Labels = mixedMoment B raw14683step1 raw14683step1Labels := by
      have ha : raw14683step1 = -raw14683step0 := by apply Matrix.ext; change ∀ i j, raw14683step1 i j = -(raw14683step0 i j); unfold raw14683step1 raw14683step0; decide +kernel
      have hl : raw14683step1Labels = raw14683step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw14684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14684Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw14684step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14684step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw14684step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14684 raw14684Labels = mixedMoment B node3899 node3899Labels := by
  calc
    mixedMoment B raw14684 raw14684Labels = mixedMoment B raw14684step0 raw14684step0Labels := by
      have ha : raw14684step0 = (fun i j => raw14684 (permutation632 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14684step0 raw14684; decide +kernel
      have hl : raw14684step0Labels = raw14684Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14684 raw14684Labels permutation632 permutation2
    mixedMoment B raw14684step0 raw14684step0Labels = mixedMoment B raw14684step1 raw14684step1Labels := by
      have ha : raw14684step1 = -raw14684step0 := by apply Matrix.ext; change ∀ i j, raw14684step1 i j = -(raw14684step0 i j); unfold raw14684step1 raw14684step0; decide +kernel
      have hl : raw14684step1Labels = raw14684step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3899 node3899Labels := by rfl

def raw14685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14685Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14685step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14685step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14685 raw14685Labels = mixedMoment B node3964 node3964Labels := by
  calc
    mixedMoment B raw14685 raw14685Labels = mixedMoment B raw14685step0 raw14685step0Labels := by
      have ha : raw14685step0 = (fun i j => raw14685 (permutation536 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14685step0 raw14685; decide +kernel
      have hl : raw14685step0Labels = raw14685Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14685 raw14685Labels permutation536 permutation4
    _ = mixedMoment B node3964 node3964Labels := by rfl

def raw14686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14686Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14686step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw14686step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14686step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw14686step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14686 raw14686Labels = mixedMoment B node3783 node3783Labels := by
  calc
    mixedMoment B raw14686 raw14686Labels = mixedMoment B raw14686step0 raw14686step0Labels := by
      have ha : raw14686step0 = (fun i j => raw14686 (permutation645 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14686step0 raw14686; decide +kernel
      have hl : raw14686step0Labels = raw14686Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14686 raw14686Labels permutation645 permutation2
    mixedMoment B raw14686step0 raw14686step0Labels = mixedMoment B raw14686step1 raw14686step1Labels := by
      have ha : raw14686step1 = -raw14686step0 := by apply Matrix.ext; change ∀ i j, raw14686step1 i j = -(raw14686step0 i j); unfold raw14686step1 raw14686step0; decide +kernel
      have hl : raw14686step1Labels = raw14686step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3783 node3783Labels := by rfl

def raw14687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14687Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14687step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, 1, 1]]
def raw14687step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14687step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw14687step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14687 raw14687Labels = mixedMoment B node3863 node3863Labels := by
  calc
    mixedMoment B raw14687 raw14687Labels = mixedMoment B raw14687step0 raw14687step0Labels := by
      have ha : raw14687step0 = (fun i j => raw14687 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14687step0 raw14687; decide +kernel
      have hl : raw14687step0Labels = raw14687Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14687 raw14687Labels permutation663 permutation2
    mixedMoment B raw14687step0 raw14687step0Labels = mixedMoment B raw14687step1 raw14687step1Labels := by
      have ha : raw14687step1 = -raw14687step0 := by apply Matrix.ext; change ∀ i j, raw14687step1 i j = -(raw14687step0 i j); unfold raw14687step1 raw14687step0; decide +kernel
      have hl : raw14687step1Labels = raw14687step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3863 node3863Labels := by rfl

def raw14688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14688Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw14688step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14688 raw14688Labels = mixedMoment B node2945 node2945Labels := by
  calc
    mixedMoment B raw14688 raw14688Labels = mixedMoment B raw14688step0 raw14688step0Labels := by
      have ha : raw14688step0 = (fun i j => raw14688 (permutation566 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14688step0 raw14688; decide +kernel
      have hl : raw14688step0Labels = raw14688Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14688 raw14688Labels permutation566 permutation4
    _ = mixedMoment B node2945 node2945Labels := by rfl

def raw14689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14689Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14689step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw14689step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14689step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw14689step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14689 raw14689Labels = mixedMoment B node2612 node2612Labels := by
  calc
    mixedMoment B raw14689 raw14689Labels = mixedMoment B raw14689step0 raw14689step0Labels := by
      have ha : raw14689step0 = (fun i j => raw14689 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14689step0 raw14689; decide +kernel
      have hl : raw14689step0Labels = raw14689Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14689 raw14689Labels permutation681 permutation2
    mixedMoment B raw14689step0 raw14689step0Labels = mixedMoment B raw14689step1 raw14689step1Labels := by
      have ha : raw14689step1 = -raw14689step0 := by apply Matrix.ext; change ∀ i j, raw14689step1 i j = -(raw14689step0 i j); unfold raw14689step1 raw14689step0; decide +kernel
      have hl : raw14689step1Labels = raw14689step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2612 node2612Labels := by rfl

def raw14690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14690Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14690step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14690step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14690step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14690step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14690 raw14690Labels = mixedMoment B node3789 node3789Labels := by
  calc
    mixedMoment B raw14690 raw14690Labels = mixedMoment B raw14690step0 raw14690step0Labels := by
      have ha : raw14690step0 = (fun i j => raw14690 (permutation644 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14690step0 raw14690; decide +kernel
      have hl : raw14690step0Labels = raw14690Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14690 raw14690Labels permutation644 permutation2
    mixedMoment B raw14690step0 raw14690step0Labels = mixedMoment B raw14690step1 raw14690step1Labels := by
      have ha : raw14690step1 = -raw14690step0 := by apply Matrix.ext; change ∀ i j, raw14690step1 i j = -(raw14690step0 i j); unfold raw14690step1 raw14690step0; decide +kernel
      have hl : raw14690step1Labels = raw14690step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3789 node3789Labels := by rfl

def raw14691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14691Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14691step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14691step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14691step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14691step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14691 raw14691Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw14691 raw14691Labels = mixedMoment B raw14691step0 raw14691step0Labels := by
      have ha : raw14691step0 = (fun i j => raw14691 (permutation640 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14691step0 raw14691; decide +kernel
      have hl : raw14691step0Labels = raw14691Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14691 raw14691Labels permutation640 permutation2
    mixedMoment B raw14691step0 raw14691step0Labels = mixedMoment B raw14691step1 raw14691step1Labels := by
      have ha : raw14691step1 = -raw14691step0 := by apply Matrix.ext; change ∀ i j, raw14691step1 i j = -(raw14691step0 i j); unfold raw14691step1 raw14691step0; decide +kernel
      have hl : raw14691step1Labels = raw14691step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3801 node3801Labels := by rfl

def raw14692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14692Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14692step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14692step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14692 raw14692Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw14692 raw14692Labels = mixedMoment B raw14692step0 raw14692step0Labels := by
      have ha : raw14692step0 = (fun i j => raw14692 (permutation557 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14692step0 raw14692; decide +kernel
      have hl : raw14692step0Labels = raw14692Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14692 raw14692Labels permutation557 permutation4
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw14693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw14693Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14693step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14693step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw14693step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14693 raw14693Labels = mixedMoment B node3865 node3865Labels := by
  calc
    mixedMoment B raw14693 raw14693Labels = mixedMoment B raw14693step0 raw14693step0Labels := by
      have ha : raw14693step0 = (fun i j => raw14693 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14693step0 raw14693; decide +kernel
      have hl : raw14693step0Labels = raw14693Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14693 raw14693Labels permutation664 permutation2
    mixedMoment B raw14693step0 raw14693step0Labels = mixedMoment B raw14693step1 raw14693step1Labels := by
      have ha : raw14693step1 = -raw14693step0 := by apply Matrix.ext; change ∀ i j, raw14693step1 i j = -(raw14693step0 i j); unfold raw14693step1 raw14693step0; decide +kernel
      have hl : raw14693step1Labels = raw14693step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3865 node3865Labels := by rfl

def raw14694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14694Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14694step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14694step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14694 raw14694Labels = mixedMoment B node2920 node2920Labels := by
  calc
    mixedMoment B raw14694 raw14694Labels = mixedMoment B raw14694step0 raw14694step0Labels := by
      have ha : raw14694step0 = (fun i j => raw14694 (permutation558 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14694step0 raw14694; decide +kernel
      have hl : raw14694step0Labels = raw14694Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14694 raw14694Labels permutation558 permutation4
    _ = mixedMoment B node2920 node2920Labels := by rfl

def raw14695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14695Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14695step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14695step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14695step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw14695step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14695 raw14695Labels = mixedMoment B node2623 node2623Labels := by
  calc
    mixedMoment B raw14695 raw14695Labels = mixedMoment B raw14695step0 raw14695step0Labels := by
      have ha : raw14695step0 = (fun i j => raw14695 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14695step0 raw14695; decide +kernel
      have hl : raw14695step0Labels = raw14695Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14695 raw14695Labels permutation688 permutation2
    mixedMoment B raw14695step0 raw14695step0Labels = mixedMoment B raw14695step1 raw14695step1Labels := by
      have ha : raw14695step1 = -raw14695step0 := by apply Matrix.ext; change ∀ i j, raw14695step1 i j = -(raw14695step0 i j); unfold raw14695step1 raw14695step0; decide +kernel
      have hl : raw14695step1Labels = raw14695step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2623 node2623Labels := by rfl

def raw14696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw14696Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14696step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14696step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14696step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14696step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14696 raw14696Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw14696 raw14696Labels = mixedMoment B raw14696step0 raw14696step0Labels := by
      have ha : raw14696step0 = (fun i j => raw14696 (permutation658 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14696step0 raw14696; decide +kernel
      have hl : raw14696step0Labels = raw14696Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14696 raw14696Labels permutation658 permutation2
    mixedMoment B raw14696step0 raw14696step0Labels = mixedMoment B raw14696step1 raw14696step1Labels := by
      have ha : raw14696step1 = -raw14696step0 := by apply Matrix.ext; change ∀ i j, raw14696step1 i j = -(raw14696step0 i j); unfold raw14696step1 raw14696step0; decide +kernel
      have hl : raw14696step1Labels = raw14696step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw14697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -2, 1], ![1, 1, -2]]
def raw14697Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14697step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14697step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14697 raw14697Labels = mixedMoment B node3922 node3922Labels := by
  calc
    mixedMoment B raw14697 raw14697Labels = mixedMoment B raw14697step0 raw14697step0Labels := by
      have ha : raw14697step0 = (fun i j => raw14697 (permutation492 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14697step0 raw14697; decide +kernel
      have hl : raw14697step0Labels = raw14697Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14697 raw14697Labels permutation492 permutation4
    _ = mixedMoment B node3922 node3922Labels := by rfl

def raw14698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, -3, 1], ![2, 0, -2]]
def raw14698Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14698step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14698 raw14698Labels = mixedMoment B node3069 node3069Labels := by
  calc
    mixedMoment B raw14698 raw14698Labels = mixedMoment B raw14698step0 raw14698step0Labels := by
      have ha : raw14698step0 = (fun i j => raw14698 (permutation537 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14698step0 raw14698; decide +kernel
      have hl : raw14698step0Labels = raw14698Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14698 raw14698Labels permutation537 permutation4
    _ = mixedMoment B node3069 node3069Labels := by rfl

def raw14699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![3, -1, -2]]
def raw14699Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14699step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14699step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14699step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14699step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14699 raw14699Labels = mixedMoment B node2617 node2617Labels := by
  calc
    mixedMoment B raw14699 raw14699Labels = mixedMoment B raw14699step0 raw14699step0Labels := by
      have ha : raw14699step0 = (fun i j => raw14699 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14699step0 raw14699; decide +kernel
      have hl : raw14699step0Labels = raw14699Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14699 raw14699Labels permutation680 permutation2
    mixedMoment B raw14699step0 raw14699step0Labels = mixedMoment B raw14699step1 raw14699step1Labels := by
      have ha : raw14699step1 = -raw14699step0 := by apply Matrix.ext; change ∀ i j, raw14699step1 i j = -(raw14699step0 i j); unfold raw14699step1 raw14699step0; decide +kernel
      have hl : raw14699step1Labels = raw14699step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2617 node2617Labels := by rfl

def raw14700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -3, 1], ![1, 1, -2]]
def raw14700Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14700step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14700step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14700 raw14700Labels = mixedMoment B node2928 node2928Labels := by
  calc
    mixedMoment B raw14700 raw14700Labels = mixedMoment B raw14700step0 raw14700step0Labels := by
      have ha : raw14700step0 = (fun i j => raw14700 (permutation557 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14700step0 raw14700; decide +kernel
      have hl : raw14700step0Labels = raw14700Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14700 raw14700Labels permutation557 permutation4
    _ = mixedMoment B node2928 node2928Labels := by rfl

def raw14701 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14701Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14701step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw14701step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14701 raw14701Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw14701 raw14701Labels = mixedMoment B raw14701step0 raw14701step0Labels := by
      have ha : raw14701step0 = (fun i j => raw14701 (permutation634 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14701step0 raw14701; decide +kernel
      have hl : raw14701step0Labels = raw14701Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14701 raw14701Labels permutation634 permutation2
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw14702 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14702Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14702step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14702 raw14702Labels = mixedMoment B node5382 node5382Labels := by
  calc
    mixedMoment B raw14702 raw14702Labels = mixedMoment B raw14702step0 raw14702step0Labels := by
      have ha : raw14702step0 = (fun i j => raw14702 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14702step0 raw14702; decide +kernel
      have hl : raw14702step0Labels = raw14702Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14702 raw14702Labels permutation646 permutation2
    _ = mixedMoment B node5382 node5382Labels := by rfl

def raw14703 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14703Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14703step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw14703step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14703 raw14703Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw14703 raw14703Labels = mixedMoment B raw14703step0 raw14703step0Labels := by
      have hz : ∀ j, raw14703 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14703step0 = (fun i j => raw14703 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14703step0 raw14703; decide +kernel
      have hl : raw14703step0Labels = raw14703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14703 raw14703Labels permutation434 hz
    mixedMoment B raw14703step0 raw14703step0Labels = mixedMoment B raw14703step1 raw14703step1Labels := by
      have ha : raw14703step1 = (fun i j => raw14703step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14703step1 raw14703step0; decide +kernel
      have hl : raw14703step1Labels = raw14703step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14703step0 raw14703step0Labels permutation145 permutation2
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw14704 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14704Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14704step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw14704step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14704step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14704step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14704step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14704step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14704 raw14704Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw14704 raw14704Labels = mixedMoment B raw14704step0 raw14704step0Labels := by
      have ha : raw14704step0 = (fun i j => raw14704 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14704step0 raw14704; decide +kernel
      have hl : raw14704step0Labels = raw14704Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14704 raw14704Labels permutation682 permutation7
    mixedMoment B raw14704step0 raw14704step0Labels = mixedMoment B raw14704step1 raw14704step1Labels := by
      have ha : raw14704step1 = -raw14704step0 := by apply Matrix.ext; change ∀ i j, raw14704step1 i j = -(raw14704step0 i j); unfold raw14704step1 raw14704step0; decide +kernel
      have hl : raw14704step1Labels = raw14704step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14704step1 raw14704step1Labels = mixedMoment B raw14704step2 raw14704step2Labels := by
      have ha : raw14704step2 = raw14704step1 := by apply Matrix.ext; unfold raw14704step2 raw14704step1; decide +kernel
      have hl : raw14704step1Labels = labelEmbedding10 ∘ raw14704step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14704step1 raw14704step1Labels raw14704step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw14705 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14705Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14705step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw14705step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14705 raw14705Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw14705 raw14705Labels = mixedMoment B raw14705step0 raw14705step0Labels := by
      have ha : raw14705step0 = (fun i j => raw14705 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14705step0 raw14705; decide +kernel
      have hl : raw14705step0Labels = raw14705Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14705 raw14705Labels permutation646 permutation2
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw14706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14706Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14706step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14706step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14706step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14706step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14706step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14706step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14706 raw14706Labels = mixedMoment B node5153 node5153Labels := by
  calc
    mixedMoment B raw14706 raw14706Labels = mixedMoment B raw14706step0 raw14706step0Labels := by
      have ha : raw14706step0 = (fun i j => raw14706 (permutation194 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14706step0 raw14706; decide +kernel
      have hl : raw14706step0Labels = raw14706Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14706 raw14706Labels permutation194 permutation4
    mixedMoment B raw14706step0 raw14706step0Labels = mixedMoment B raw14706step1 raw14706step1Labels := by
      have ha : raw14706step1 = -raw14706step0 := by apply Matrix.ext; change ∀ i j, raw14706step1 i j = -(raw14706step0 i j); unfold raw14706step1 raw14706step0; decide +kernel
      have hl : raw14706step1Labels = raw14706step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14706step1 raw14706step1Labels = mixedMoment B raw14706step2 raw14706step2Labels := by
      have ha : raw14706step2 = raw14706step1 := by apply Matrix.ext; unfold raw14706step2 raw14706step1; decide +kernel
      have hl : raw14706step1Labels = labelEmbedding7 ∘ raw14706step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14706step1 raw14706step1Labels raw14706step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5153 node5153Labels := by rfl

def raw14707 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14707Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14707step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14707step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14707step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw14707step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14707 raw14707Labels = mixedMoment B node5375 node5375Labels := by
  calc
    mixedMoment B raw14707 raw14707Labels = mixedMoment B raw14707step0 raw14707step0Labels := by
      have ha : raw14707step0 = (fun i j => raw14707 (permutation416 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14707step0 raw14707; decide +kernel
      have hl : raw14707step0Labels = raw14707Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14707 raw14707Labels permutation416 permutation3
    mixedMoment B raw14707step0 raw14707step0Labels = mixedMoment B raw14707step1 raw14707step1Labels := by
      have ha : raw14707step1 = raw14707step0 := by apply Matrix.ext; unfold raw14707step1 raw14707step0; decide +kernel
      have hl : raw14707step0Labels = labelEmbedding6 ∘ raw14707step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14707step0 raw14707step0Labels raw14707step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5375 node5375Labels := by rfl

def raw14708 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14708Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14708step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw14708step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14708 raw14708Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw14708 raw14708Labels = mixedMoment B raw14708step0 raw14708step0Labels := by
      have hz : ∀ j, raw14708 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14708step0 = (fun i j => raw14708 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14708step0 raw14708; decide +kernel
      have hl : raw14708step0Labels = raw14708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14708 raw14708Labels permutation434 hz
    mixedMoment B raw14708step0 raw14708step0Labels = mixedMoment B raw14708step1 raw14708step1Labels := by
      have ha : raw14708step1 = (fun i j => raw14708step0 (permutation141 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14708step1 raw14708step0; decide +kernel
      have hl : raw14708step1Labels = raw14708step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14708step0 raw14708step0Labels permutation141 permutation2
    _ = mixedMoment B node5436 node5436Labels := by rfl

def raw14709 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14709Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14709step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14709step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14709step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14709step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14709step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14709step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14709 raw14709Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw14709 raw14709Labels = mixedMoment B raw14709step0 raw14709step0Labels := by
      have ha : raw14709step0 = (fun i j => raw14709 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14709step0 raw14709; decide +kernel
      have hl : raw14709step0Labels = raw14709Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14709 raw14709Labels permutation682 permutation7
    mixedMoment B raw14709step0 raw14709step0Labels = mixedMoment B raw14709step1 raw14709step1Labels := by
      have ha : raw14709step1 = -raw14709step0 := by apply Matrix.ext; change ∀ i j, raw14709step1 i j = -(raw14709step0 i j); unfold raw14709step1 raw14709step0; decide +kernel
      have hl : raw14709step1Labels = raw14709step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14709step1 raw14709step1Labels = mixedMoment B raw14709step2 raw14709step2Labels := by
      have ha : raw14709step2 = raw14709step1 := by apply Matrix.ext; unfold raw14709step2 raw14709step1; decide +kernel
      have hl : raw14709step1Labels = labelEmbedding10 ∘ raw14709step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14709step1 raw14709step1Labels raw14709step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw14710 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14710Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14710step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw14710step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14710 raw14710Labels = mixedMoment B node5153 node5153Labels := by
  calc
    mixedMoment B raw14710 raw14710Labels = mixedMoment B raw14710step0 raw14710step0Labels := by
      have ha : raw14710step0 = (fun i j => raw14710 (permutation628 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14710step0 raw14710; decide +kernel
      have hl : raw14710step0Labels = raw14710Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14710 raw14710Labels permutation628 permutation2
    _ = mixedMoment B node5153 node5153Labels := by rfl

def raw14711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14711Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14711step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14711step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14711step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw14711step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14711step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14711step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14711step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14711step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14711 raw14711Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw14711 raw14711Labels = mixedMoment B raw14711step0 raw14711step0Labels := by
      have hz : ∀ j, raw14711 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14711step0 = (fun i j => raw14711 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14711step0 raw14711; decide +kernel
      have hl : raw14711step0Labels = raw14711Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14711 raw14711Labels permutation346 hz
    mixedMoment B raw14711step0 raw14711step0Labels = mixedMoment B raw14711step1 raw14711step1Labels := by
      have ha : raw14711step1 = (fun i j => raw14711step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14711step1 raw14711step0; decide +kernel
      have hl : raw14711step1Labels = raw14711step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14711step0 raw14711step0Labels permutation36 permutation4
    mixedMoment B raw14711step1 raw14711step1Labels = mixedMoment B raw14711step2 raw14711step2Labels := by
      have ha : raw14711step2 = -raw14711step1 := by apply Matrix.ext; change ∀ i j, raw14711step2 i j = -(raw14711step1 i j); unfold raw14711step2 raw14711step1; decide +kernel
      have hl : raw14711step2Labels = raw14711step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14711step2 raw14711step2Labels = mixedMoment B raw14711step3 raw14711step3Labels := by
      have ha : raw14711step3 = raw14711step2 := by apply Matrix.ext; unfold raw14711step3 raw14711step2; decide +kernel
      have hl : raw14711step2Labels = labelEmbedding7 ∘ raw14711step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14711step2 raw14711step2Labels raw14711step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw14712 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14712Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14712step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14712step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14712step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14712step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14712step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14712step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14712 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14712 raw14712Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw14712 raw14712Labels = mixedMoment B raw14712step0 raw14712step0Labels := by
      have hz : ∀ j, raw14712 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14712step0 = (fun i j => raw14712 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14712step0 raw14712; decide +kernel
      have hl : raw14712step0Labels = raw14712Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14712 raw14712Labels permutation346 hz
    mixedMoment B raw14712step0 raw14712step0Labels = mixedMoment B raw14712step1 raw14712step1Labels := by
      have ha : raw14712step1 = (fun i j => raw14712step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14712step1 raw14712step0; decide +kernel
      have hl : raw14712step1Labels = raw14712step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14712step0 raw14712step0Labels permutation32 permutation6
    mixedMoment B raw14712step1 raw14712step1Labels = mixedMoment B raw14712step2 raw14712step2Labels := by
      have ha : raw14712step2 = raw14712step1 := by apply Matrix.ext; unfold raw14712step2 raw14712step1; decide +kernel
      have hl : raw14712step1Labels = labelEmbedding9 ∘ raw14712step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14712step1 raw14712step1Labels raw14712step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw14713 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14713Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14713step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14713step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14713step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 0, 2]]
def raw14713step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14713step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14713step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14713step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14713step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14713 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14713 raw14713Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw14713 raw14713Labels = mixedMoment B raw14713step0 raw14713step0Labels := by
      have hz : ∀ j, raw14713 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw14713step0 = (fun i j => raw14713 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw14713step0 raw14713; decide +kernel
      have hl : raw14713step0Labels = raw14713Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14713 raw14713Labels permutation434 hz
    mixedMoment B raw14713step0 raw14713step0Labels = mixedMoment B raw14713step1 raw14713step1Labels := by
      have hz : ∀ j, raw14713step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14713step1 = (fun i j => raw14713step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14713step1 raw14713step0; decide +kernel
      have hl : raw14713step1Labels = raw14713step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14713step0 raw14713step0Labels permutation80 hz
    mixedMoment B raw14713step1 raw14713step1Labels = mixedMoment B raw14713step2 raw14713step2Labels := by
      have ha : raw14713step2 = (fun i j => raw14713step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14713step2 raw14713step1; decide +kernel
      have hl : raw14713step2Labels = raw14713step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14713step1 raw14713step1Labels permutation8 permutation6
    mixedMoment B raw14713step2 raw14713step2Labels = mixedMoment B raw14713step3 raw14713step3Labels := by
      have ha : raw14713step3 = raw14713step2 := by apply Matrix.ext; unfold raw14713step3 raw14713step2; decide +kernel
      have hl : raw14713step2Labels = labelEmbedding9 ∘ raw14713step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14713step2 raw14713step2Labels raw14713step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw14714 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14714Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14714step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14714step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14714step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14714step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14714step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14714step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14714 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14714 raw14714Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw14714 raw14714Labels = mixedMoment B raw14714step0 raw14714step0Labels := by
      have hz : ∀ j, raw14714 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14714step0 = (fun i j => raw14714 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14714step0 raw14714; decide +kernel
      have hl : raw14714step0Labels = raw14714Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14714 raw14714Labels permutation346 hz
    mixedMoment B raw14714step0 raw14714step0Labels = mixedMoment B raw14714step1 raw14714step1Labels := by
      have ha : raw14714step1 = (fun i j => raw14714step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14714step1 raw14714step0; decide +kernel
      have hl : raw14714step1Labels = raw14714step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14714step0 raw14714step0Labels permutation32 permutation6
    mixedMoment B raw14714step1 raw14714step1Labels = mixedMoment B raw14714step2 raw14714step2Labels := by
      have ha : raw14714step2 = raw14714step1 := by apply Matrix.ext; unfold raw14714step2 raw14714step1; decide +kernel
      have hl : raw14714step1Labels = labelEmbedding9 ∘ raw14714step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14714step1 raw14714step1Labels raw14714step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw14715 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14715Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14715step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 1, 2]]
def raw14715step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14715step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14715step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14715 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14715 raw14715Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw14715 raw14715Labels = mixedMoment B raw14715step0 raw14715step0Labels := by
      have hz : ∀ j, raw14715 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14715step0 = (fun i j => raw14715 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14715step0 raw14715; decide +kernel
      have hl : raw14715step0Labels = raw14715Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14715 raw14715Labels permutation346 hz
    mixedMoment B raw14715step0 raw14715step0Labels = mixedMoment B raw14715step1 raw14715step1Labels := by
      have ha : raw14715step1 = (fun i j => raw14715step0 (permutation133 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14715step1 raw14715step0; decide +kernel
      have hl : raw14715step1Labels = raw14715step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14715step0 raw14715step0Labels permutation133 permutation2
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw14716 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14716Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14716step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw14716step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14716step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14716step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14716step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14716step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14716 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14716 raw14716Labels = mixedMoment B node5131 node5131Labels := by
  calc
    mixedMoment B raw14716 raw14716Labels = mixedMoment B raw14716step0 raw14716step0Labels := by
      have ha : raw14716step0 = (fun i j => raw14716 (permutation180 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14716step0 raw14716; decide +kernel
      have hl : raw14716step0Labels = raw14716Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14716 raw14716Labels permutation180 permutation4
    mixedMoment B raw14716step0 raw14716step0Labels = mixedMoment B raw14716step1 raw14716step1Labels := by
      have ha : raw14716step1 = -raw14716step0 := by apply Matrix.ext; change ∀ i j, raw14716step1 i j = -(raw14716step0 i j); unfold raw14716step1 raw14716step0; decide +kernel
      have hl : raw14716step1Labels = raw14716step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14716step1 raw14716step1Labels = mixedMoment B raw14716step2 raw14716step2Labels := by
      have ha : raw14716step2 = raw14716step1 := by apply Matrix.ext; unfold raw14716step2 raw14716step1; decide +kernel
      have hl : raw14716step1Labels = labelEmbedding7 ∘ raw14716step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14716step1 raw14716step1Labels raw14716step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5131 node5131Labels := by rfl

def raw14717 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![-1, 1, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14717Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14717step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14717step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14717step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14717step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14717 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14717 raw14717Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw14717 raw14717Labels = mixedMoment B raw14717step0 raw14717step0Labels := by
      have ha : raw14717step0 = (fun i j => raw14717 (permutation502 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14717step0 raw14717; decide +kernel
      have hl : raw14717step0Labels = raw14717Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14717 raw14717Labels permutation502 permutation5
    mixedMoment B raw14717step0 raw14717step0Labels = mixedMoment B raw14717step1 raw14717step1Labels := by
      have ha : raw14717step1 = raw14717step0 := by apply Matrix.ext; unfold raw14717step1 raw14717step0; decide +kernel
      have hl : raw14717step0Labels = labelEmbedding8 ∘ raw14717step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14717step0 raw14717step0Labels raw14717step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5360 node5360Labels := by rfl

def raw14718 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-2, 2, 0], ![2, -2, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw14718Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14718step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14718step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14718step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw14718step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14718 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14718 raw14718Labels = mixedMoment B node5342 node5342Labels := by
  calc
    mixedMoment B raw14718 raw14718Labels = mixedMoment B raw14718step0 raw14718step0Labels := by
      have ha : raw14718step0 = (fun i j => raw14718 (permutation493 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14718step0 raw14718; decide +kernel
      have hl : raw14718step0Labels = raw14718Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14718 raw14718Labels permutation493 permutation5
    mixedMoment B raw14718step0 raw14718step0Labels = mixedMoment B raw14718step1 raw14718step1Labels := by
      have ha : raw14718step1 = raw14718step0 := by apply Matrix.ext; unfold raw14718step1 raw14718step0; decide +kernel
      have hl : raw14718step0Labels = labelEmbedding8 ∘ raw14718step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14718step0 raw14718step0Labels raw14718step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5342 node5342Labels := by rfl

def raw14719 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw14719Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14719step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14719step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14719 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14719 raw14719Labels = mixedMoment B node5426 node5426Labels := by
  calc
    mixedMoment B raw14719 raw14719Labels = mixedMoment B raw14719step0 raw14719step0Labels := by
      have ha : raw14719step0 = (fun i j => raw14719 (permutation641 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14719step0 raw14719; decide +kernel
      have hl : raw14719step0Labels = raw14719Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14719 raw14719Labels permutation641 permutation2
    _ = mixedMoment B node5426 node5426Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
