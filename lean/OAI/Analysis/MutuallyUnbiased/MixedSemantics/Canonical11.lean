import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1408 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 3, -3]]
def raw1408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1408step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw1408step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1408 raw1408Labels = mixedMoment B node1190 node1190Labels := by
  calc
    mixedMoment B raw1408 raw1408Labels = mixedMoment B raw1408step0 raw1408step0Labels := by
      have ha : raw1408step0 = (fun i j => raw1408 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1408step0 raw1408; decide +kernel
      have hl : raw1408step0Labels = raw1408Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1408 raw1408Labels permutation8 permutation4
    _ = mixedMoment B node1190 node1190Labels := by rfl

def raw1409 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 3, -3]]
def raw1409Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1409step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, -2, 0], ![2, 2, -4]]
def raw1409step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1409step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, -2, 0], ![2, 2, -4]]
def raw1409step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1409 raw1409Labels = mixedMoment B node1952 node1952Labels := by
  calc
    mixedMoment B raw1409 raw1409Labels = mixedMoment B raw1409step0 raw1409step0Labels := by
      have ha : raw1409step0 = (fun i j => raw1409 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1409step0 raw1409; decide +kernel
      have hl : raw1409step0Labels = raw1409Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1409 raw1409Labels permutation31 permutation6
    mixedMoment B raw1409step0 raw1409step0Labels = mixedMoment B raw1409step1 raw1409step1Labels := by
      have ha : raw1409step1 = raw1409step0 := by apply Matrix.ext; unfold raw1409step1 raw1409step0; decide +kernel
      have hl : raw1409step0Labels = labelEmbedding1 ∘ raw1409step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1409step0 raw1409step0Labels raw1409step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1952 node1952Labels := by rfl

def raw1410 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 2, -2], ![0, 2, -2]]
def raw1410Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1410step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw1410step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1410step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw1410step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1410 raw1410Labels = mixedMoment B node4575 node4575Labels := by
  calc
    mixedMoment B raw1410 raw1410Labels = mixedMoment B raw1410step0 raw1410step0Labels := by
      have ha : raw1410step0 = (fun i j => raw1410 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1410step0 raw1410; decide +kernel
      have hl : raw1410step0Labels = raw1410Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1410 raw1410Labels permutation8 permutation4
    mixedMoment B raw1410step0 raw1410step0Labels = mixedMoment B raw1410step1 raw1410step1Labels := by
      have ha : raw1410step1 = raw1410step0 := by apply Matrix.ext; unfold raw1410step1 raw1410step0; decide +kernel
      have hl : raw1410step0Labels = labelEmbedding7 ∘ raw1410step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1410step0 raw1410step0Labels raw1410step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4575 node4575Labels := by rfl

def raw1411 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 2, -2], ![0, 2, -2]]
def raw1411Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1411step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw1411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1411 raw1411Labels = mixedMoment B node1193 node1193Labels := by
  calc
    mixedMoment B raw1411 raw1411Labels = mixedMoment B raw1411step0 raw1411step0Labels := by
      have ha : raw1411step0 = (fun i j => raw1411 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1411step0 raw1411; decide +kernel
      have hl : raw1411step0Labels = raw1411Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1411 raw1411Labels permutation8 permutation4
    _ = mixedMoment B node1193 node1193Labels := by rfl

def raw1412 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 2, -2], ![0, 2, -2]]
def raw1412Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1412step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw1412step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1412step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1412step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1412step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1412step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1412 raw1412Labels = mixedMoment B node3248 node3248Labels := by
  calc
    mixedMoment B raw1412 raw1412Labels = mixedMoment B raw1412step0 raw1412step0Labels := by
      have ha : raw1412step0 = (fun i j => raw1412 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1412step0 raw1412; decide +kernel
      have hl : raw1412step0Labels = raw1412Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1412 raw1412Labels permutation8 permutation6
    mixedMoment B raw1412step0 raw1412step0Labels = mixedMoment B raw1412step1 raw1412step1Labels := by
      have ha : raw1412step1 = -raw1412step0 := by apply Matrix.ext; change ∀ i j, raw1412step1 i j = -(raw1412step0 i j); unfold raw1412step1 raw1412step0; decide +kernel
      have hl : raw1412step1Labels = raw1412step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1412step1 raw1412step1Labels = mixedMoment B raw1412step2 raw1412step2Labels := by
      have ha : raw1412step2 = raw1412step1 := by apply Matrix.ext; unfold raw1412step2 raw1412step1; decide +kernel
      have hl : raw1412step1Labels = labelEmbedding1 ∘ raw1412step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1412step1 raw1412step1Labels raw1412step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3248 node3248Labels := by rfl

def raw1413 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1413Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1413step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1413step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1413step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1413 raw1413Labels = mixedMoment B node4581 node4581Labels := by
  calc
    mixedMoment B raw1413 raw1413Labels = mixedMoment B raw1413step0 raw1413step0Labels := by
      have ha : raw1413step0 = (fun i j => raw1413 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1413step0 raw1413; decide +kernel
      have hl : raw1413step0Labels = raw1413Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1413 raw1413Labels permutation152 permutation4
    mixedMoment B raw1413step0 raw1413step0Labels = mixedMoment B raw1413step1 raw1413step1Labels := by
      have ha : raw1413step1 = raw1413step0 := by apply Matrix.ext; unfold raw1413step1 raw1413step0; decide +kernel
      have hl : raw1413step0Labels = labelEmbedding7 ∘ raw1413step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1413step0 raw1413step0Labels raw1413step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4581 node4581Labels := by rfl

def raw1414 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1414Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1414 raw1414Labels = mixedMoment B node1200 node1200Labels := by
  calc
    mixedMoment B raw1414 raw1414Labels = mixedMoment B raw1414step0 raw1414step0Labels := by
      have ha : raw1414step0 = (fun i j => raw1414 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1414step0 raw1414; decide +kernel
      have hl : raw1414step0Labels = raw1414Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1414 raw1414Labels permutation152 permutation4
    _ = mixedMoment B node1200 node1200Labels := by rfl

def raw1415 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1415Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1415step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1415step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1415step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1415step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1415step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1415 raw1415Labels = mixedMoment B node3281 node3281Labels := by
  calc
    mixedMoment B raw1415 raw1415Labels = mixedMoment B raw1415step0 raw1415step0Labels := by
      have ha : raw1415step0 = (fun i j => raw1415 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1415step0 raw1415; decide +kernel
      have hl : raw1415step0Labels = raw1415Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1415 raw1415Labels permutation152 permutation6
    mixedMoment B raw1415step0 raw1415step0Labels = mixedMoment B raw1415step1 raw1415step1Labels := by
      have ha : raw1415step1 = -raw1415step0 := by apply Matrix.ext; change ∀ i j, raw1415step1 i j = -(raw1415step0 i j); unfold raw1415step1 raw1415step0; decide +kernel
      have hl : raw1415step1Labels = raw1415step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1415step1 raw1415step1Labels = mixedMoment B raw1415step2 raw1415step2Labels := by
      have ha : raw1415step2 = raw1415step1 := by apply Matrix.ext; unfold raw1415step2 raw1415step1; decide +kernel
      have hl : raw1415step1Labels = labelEmbedding1 ∘ raw1415step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1415step1 raw1415step1Labels raw1415step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3281 node3281Labels := by rfl

def raw1416 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1416step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1416step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1416 raw1416Labels = mixedMoment B node4583 node4583Labels := by
  calc
    mixedMoment B raw1416 raw1416Labels = mixedMoment B raw1416step0 raw1416step0Labels := by
      have ha : raw1416step0 = (fun i j => raw1416 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1416step0 raw1416; decide +kernel
      have hl : raw1416step0Labels = raw1416Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1416 raw1416Labels permutation32 permutation4
    mixedMoment B raw1416step0 raw1416step0Labels = mixedMoment B raw1416step1 raw1416step1Labels := by
      have ha : raw1416step1 = raw1416step0 := by apply Matrix.ext; unfold raw1416step1 raw1416step0; decide +kernel
      have hl : raw1416step0Labels = labelEmbedding7 ∘ raw1416step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1416step0 raw1416step0Labels raw1416step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4583 node4583Labels := by rfl

def raw1417 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1417Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1417 raw1417Labels = mixedMoment B node1202 node1202Labels := by
  calc
    mixedMoment B raw1417 raw1417Labels = mixedMoment B raw1417step0 raw1417step0Labels := by
      have ha : raw1417step0 = (fun i j => raw1417 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1417step0 raw1417; decide +kernel
      have hl : raw1417step0Labels = raw1417Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1417 raw1417Labels permutation32 permutation4
    _ = mixedMoment B node1202 node1202Labels := by rfl

def raw1418 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1418Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw1418step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw1418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1418 raw1418Labels = mixedMoment B node1942 node1942Labels := by
  calc
    mixedMoment B raw1418 raw1418Labels = mixedMoment B raw1418step0 raw1418step0Labels := by
      have ha : raw1418step0 = (fun i j => raw1418 (permutation149 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1418step0 raw1418; decide +kernel
      have hl : raw1418step0Labels = raw1418Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1418 raw1418Labels permutation149 permutation6
    mixedMoment B raw1418step0 raw1418step0Labels = mixedMoment B raw1418step1 raw1418step1Labels := by
      have ha : raw1418step1 = raw1418step0 := by apply Matrix.ext; unfold raw1418step1 raw1418step0; decide +kernel
      have hl : raw1418step0Labels = labelEmbedding1 ∘ raw1418step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1418step0 raw1418step0Labels raw1418step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1942 node1942Labels := by rfl

def raw1419 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1419step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1419step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1419 raw1419Labels = mixedMoment B node4586 node4586Labels := by
  calc
    mixedMoment B raw1419 raw1419Labels = mixedMoment B raw1419step0 raw1419step0Labels := by
      have ha : raw1419step0 = (fun i j => raw1419 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1419step0 raw1419; decide +kernel
      have hl : raw1419step0Labels = raw1419Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1419 raw1419Labels permutation32 permutation4
    mixedMoment B raw1419step0 raw1419step0Labels = mixedMoment B raw1419step1 raw1419step1Labels := by
      have ha : raw1419step1 = raw1419step0 := by apply Matrix.ext; unfold raw1419step1 raw1419step0; decide +kernel
      have hl : raw1419step0Labels = labelEmbedding7 ∘ raw1419step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1419step0 raw1419step0Labels raw1419step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4586 node4586Labels := by rfl

def raw1420 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1420Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1420step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1420 raw1420Labels = mixedMoment B node1205 node1205Labels := by
  calc
    mixedMoment B raw1420 raw1420Labels = mixedMoment B raw1420step0 raw1420step0Labels := by
      have ha : raw1420step0 = (fun i j => raw1420 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1420step0 raw1420; decide +kernel
      have hl : raw1420step0Labels = raw1420Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1420 raw1420Labels permutation32 permutation4
    _ = mixedMoment B node1205 node1205Labels := by rfl

def raw1421 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1421Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw1421step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1421step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1421step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1421step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1421step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1421 raw1421Labels = mixedMoment B node3284 node3284Labels := by
  calc
    mixedMoment B raw1421 raw1421Labels = mixedMoment B raw1421step0 raw1421step0Labels := by
      have ha : raw1421step0 = (fun i j => raw1421 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1421step0 raw1421; decide +kernel
      have hl : raw1421step0Labels = raw1421Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1421 raw1421Labels permutation32 permutation6
    mixedMoment B raw1421step0 raw1421step0Labels = mixedMoment B raw1421step1 raw1421step1Labels := by
      have ha : raw1421step1 = -raw1421step0 := by apply Matrix.ext; change ∀ i j, raw1421step1 i j = -(raw1421step0 i j); unfold raw1421step1 raw1421step0; decide +kernel
      have hl : raw1421step1Labels = raw1421step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1421step1 raw1421step1Labels = mixedMoment B raw1421step2 raw1421step2Labels := by
      have ha : raw1421step2 = raw1421step1 := by apply Matrix.ext; unfold raw1421step2 raw1421step1; decide +kernel
      have hl : raw1421step1Labels = labelEmbedding1 ∘ raw1421step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1421step1 raw1421step1Labels raw1421step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3284 node3284Labels := by rfl

def raw1422 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1422step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1422step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1422step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1422 raw1422Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw1422 raw1422Labels = mixedMoment B raw1422step0 raw1422step0Labels := by
      have ha : raw1422step0 = (fun i j => raw1422 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1422step0 raw1422; decide +kernel
      have hl : raw1422step0Labels = raw1422Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1422 raw1422Labels permutation152 permutation4
    mixedMoment B raw1422step0 raw1422step0Labels = mixedMoment B raw1422step1 raw1422step1Labels := by
      have ha : raw1422step1 = raw1422step0 := by apply Matrix.ext; unfold raw1422step1 raw1422step0; decide +kernel
      have hl : raw1422step0Labels = labelEmbedding7 ∘ raw1422step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1422step0 raw1422step0Labels raw1422step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

def raw1423 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1423Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1423 raw1423Labels = mixedMoment B node1235 node1235Labels := by
  calc
    mixedMoment B raw1423 raw1423Labels = mixedMoment B raw1423step0 raw1423step0Labels := by
      have ha : raw1423step0 = (fun i j => raw1423 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1423step0 raw1423; decide +kernel
      have hl : raw1423step0Labels = raw1423Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1423 raw1423Labels permutation152 permutation4
    _ = mixedMoment B node1235 node1235Labels := by rfl

def raw1424 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1424Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1424step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1424step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1424step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1424step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1424 raw1424Labels = mixedMoment B node3292 node3292Labels := by
  calc
    mixedMoment B raw1424 raw1424Labels = mixedMoment B raw1424step0 raw1424step0Labels := by
      have ha : raw1424step0 = (fun i j => raw1424 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1424step0 raw1424; decide +kernel
      have hl : raw1424step0Labels = raw1424Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1424 raw1424Labels permutation152 permutation6
    mixedMoment B raw1424step0 raw1424step0Labels = mixedMoment B raw1424step1 raw1424step1Labels := by
      have ha : raw1424step1 = -raw1424step0 := by apply Matrix.ext; change ∀ i j, raw1424step1 i j = -(raw1424step0 i j); unfold raw1424step1 raw1424step0; decide +kernel
      have hl : raw1424step1Labels = raw1424step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1424step1 raw1424step1Labels = mixedMoment B raw1424step2 raw1424step2Labels := by
      have ha : raw1424step2 = raw1424step1 := by apply Matrix.ext; unfold raw1424step2 raw1424step1; decide +kernel
      have hl : raw1424step1Labels = labelEmbedding1 ∘ raw1424step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1424step1 raw1424step1Labels raw1424step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3292 node3292Labels := by rfl

def raw1425 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1425step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1425step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1425 raw1425Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw1425 raw1425Labels = mixedMoment B raw1425step0 raw1425step0Labels := by
      have ha : raw1425step0 = (fun i j => raw1425 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1425step0 raw1425; decide +kernel
      have hl : raw1425step0Labels = raw1425Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1425 raw1425Labels permutation32 permutation4
    mixedMoment B raw1425step0 raw1425step0Labels = mixedMoment B raw1425step1 raw1425step1Labels := by
      have ha : raw1425step1 = raw1425step0 := by apply Matrix.ext; unfold raw1425step1 raw1425step0; decide +kernel
      have hl : raw1425step0Labels = labelEmbedding7 ∘ raw1425step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1425step0 raw1425step0Labels raw1425step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw1426 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1426Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1426 raw1426Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw1426 raw1426Labels = mixedMoment B raw1426step0 raw1426step0Labels := by
      have ha : raw1426step0 = (fun i j => raw1426 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1426step0 raw1426; decide +kernel
      have hl : raw1426step0Labels = raw1426Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1426 raw1426Labels permutation32 permutation4
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw1427 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1427Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1427step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1427step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1427step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1427step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1427 raw1427Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw1427 raw1427Labels = mixedMoment B raw1427step0 raw1427step0Labels := by
      have ha : raw1427step0 = (fun i j => raw1427 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1427step0 raw1427; decide +kernel
      have hl : raw1427step0Labels = raw1427Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1427 raw1427Labels permutation32 permutation6
    mixedMoment B raw1427step0 raw1427step0Labels = mixedMoment B raw1427step1 raw1427step1Labels := by
      have ha : raw1427step1 = -raw1427step0 := by apply Matrix.ext; change ∀ i j, raw1427step1 i j = -(raw1427step0 i j); unfold raw1427step1 raw1427step0; decide +kernel
      have hl : raw1427step1Labels = raw1427step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1427step1 raw1427step1Labels = mixedMoment B raw1427step2 raw1427step2Labels := by
      have ha : raw1427step2 = raw1427step1 := by apply Matrix.ext; unfold raw1427step2 raw1427step1; decide +kernel
      have hl : raw1427step1Labels = labelEmbedding1 ∘ raw1427step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1427step1 raw1427step1Labels raw1427step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

def raw1428 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw1428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1428step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw1428step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1428step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw1428step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1428 raw1428Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw1428 raw1428Labels = mixedMoment B raw1428step0 raw1428step0Labels := by
      have ha : raw1428step0 = (fun i j => raw1428 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1428step0 raw1428; decide +kernel
      have hl : raw1428step0Labels = raw1428Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1428 raw1428Labels permutation8 permutation4
    mixedMoment B raw1428step0 raw1428step0Labels = mixedMoment B raw1428step1 raw1428step1Labels := by
      have ha : raw1428step1 = raw1428step0 := by apply Matrix.ext; unfold raw1428step1 raw1428step0; decide +kernel
      have hl : raw1428step0Labels = labelEmbedding7 ∘ raw1428step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1428step0 raw1428step0Labels raw1428step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4605 node4605Labels := by rfl

def raw1429 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw1429Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1429step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw1429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1429 raw1429Labels = mixedMoment B node1239 node1239Labels := by
  calc
    mixedMoment B raw1429 raw1429Labels = mixedMoment B raw1429step0 raw1429step0Labels := by
      have ha : raw1429step0 = (fun i j => raw1429 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1429step0 raw1429; decide +kernel
      have hl : raw1429step0Labels = raw1429Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1429 raw1429Labels permutation8 permutation4
    _ = mixedMoment B node1239 node1239Labels := by rfl

def raw1430 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 3, -3]]
def raw1430Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1430step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw1430step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1430step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw1430step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1430 raw1430Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw1430 raw1430Labels = mixedMoment B raw1430step0 raw1430step0Labels := by
      have ha : raw1430step0 = (fun i j => raw1430 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1430step0 raw1430; decide +kernel
      have hl : raw1430step0Labels = raw1430Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1430 raw1430Labels permutation31 permutation6
    mixedMoment B raw1430step0 raw1430step0Labels = mixedMoment B raw1430step1 raw1430step1Labels := by
      have ha : raw1430step1 = raw1430step0 := by apply Matrix.ext; unfold raw1430step1 raw1430step0; decide +kernel
      have hl : raw1430step0Labels = labelEmbedding1 ∘ raw1430step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1430step0 raw1430step0Labels raw1430step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2226 node2226Labels := by rfl

def raw1431 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1431step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1431step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1431 raw1431Labels = mixedMoment B node4606 node4606Labels := by
  calc
    mixedMoment B raw1431 raw1431Labels = mixedMoment B raw1431step0 raw1431step0Labels := by
      have ha : raw1431step0 = (fun i j => raw1431 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1431step0 raw1431; decide +kernel
      have hl : raw1431step0Labels = raw1431Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1431 raw1431Labels permutation32 permutation4
    mixedMoment B raw1431step0 raw1431step0Labels = mixedMoment B raw1431step1 raw1431step1Labels := by
      have ha : raw1431step1 = raw1431step0 := by apply Matrix.ext; unfold raw1431step1 raw1431step0; decide +kernel
      have hl : raw1431step0Labels = labelEmbedding7 ∘ raw1431step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1431step0 raw1431step0Labels raw1431step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4606 node4606Labels := by rfl

def raw1432 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1432Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1432 raw1432Labels = mixedMoment B node1240 node1240Labels := by
  calc
    mixedMoment B raw1432 raw1432Labels = mixedMoment B raw1432step0 raw1432step0Labels := by
      have ha : raw1432step0 = (fun i j => raw1432 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1432step0 raw1432; decide +kernel
      have hl : raw1432step0Labels = raw1432Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1432 raw1432Labels permutation32 permutation4
    _ = mixedMoment B node1240 node1240Labels := by rfl

def raw1433 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1433Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw1433step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1433step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1433step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1433step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1433step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1433 raw1433Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw1433 raw1433Labels = mixedMoment B raw1433step0 raw1433step0Labels := by
      have ha : raw1433step0 = (fun i j => raw1433 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1433step0 raw1433; decide +kernel
      have hl : raw1433step0Labels = raw1433Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1433 raw1433Labels permutation32 permutation6
    mixedMoment B raw1433step0 raw1433step0Labels = mixedMoment B raw1433step1 raw1433step1Labels := by
      have ha : raw1433step1 = -raw1433step0 := by apply Matrix.ext; change ∀ i j, raw1433step1 i j = -(raw1433step0 i j); unfold raw1433step1 raw1433step0; decide +kernel
      have hl : raw1433step1Labels = raw1433step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1433step1 raw1433step1Labels = mixedMoment B raw1433step2 raw1433step2Labels := by
      have ha : raw1433step2 = raw1433step1 := by apply Matrix.ext; unfold raw1433step2 raw1433step1; decide +kernel
      have hl : raw1433step1Labels = labelEmbedding1 ∘ raw1433step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1433step1 raw1433step1Labels raw1433step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

def raw1434 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]
def raw1434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1434step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw1434step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1434step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw1434step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1434 raw1434Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw1434 raw1434Labels = mixedMoment B raw1434step0 raw1434step0Labels := by
      have ha : raw1434step0 = (fun i j => raw1434 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1434step0 raw1434; decide +kernel
      have hl : raw1434step0Labels = raw1434Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1434 raw1434Labels permutation8 permutation4
    mixedMoment B raw1434step0 raw1434step0Labels = mixedMoment B raw1434step1 raw1434step1Labels := by
      have ha : raw1434step1 = raw1434step0 := by apply Matrix.ext; unfold raw1434step1 raw1434step0; decide +kernel
      have hl : raw1434step0Labels = labelEmbedding7 ∘ raw1434step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1434step0 raw1434step0Labels raw1434step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

def raw1435 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]
def raw1435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1435step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw1435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1435 raw1435Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw1435 raw1435Labels = mixedMoment B raw1435step0 raw1435step0Labels := by
      have ha : raw1435step0 = (fun i j => raw1435 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1435step0 raw1435; decide +kernel
      have hl : raw1435step0Labels = raw1435Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1435 raw1435Labels permutation8 permutation4
    _ = mixedMoment B node1242 node1242Labels := by rfl

def raw1436 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2]]
def raw1436Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1436step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw1436step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1436step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1436step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1436step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1436step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1436 raw1436Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw1436 raw1436Labels = mixedMoment B raw1436step0 raw1436step0Labels := by
      have ha : raw1436step0 = (fun i j => raw1436 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1436step0 raw1436; decide +kernel
      have hl : raw1436step0Labels = raw1436Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1436 raw1436Labels permutation8 permutation6
    mixedMoment B raw1436step0 raw1436step0Labels = mixedMoment B raw1436step1 raw1436step1Labels := by
      have ha : raw1436step1 = -raw1436step0 := by apply Matrix.ext; change ∀ i j, raw1436step1 i j = -(raw1436step0 i j); unfold raw1436step1 raw1436step0; decide +kernel
      have hl : raw1436step1Labels = raw1436step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1436step1 raw1436step1Labels = mixedMoment B raw1436step2 raw1436step2Labels := by
      have ha : raw1436step2 = raw1436step1 := by apply Matrix.ext; unfold raw1436step2 raw1436step1; decide +kernel
      have hl : raw1436step1Labels = labelEmbedding1 ∘ raw1436step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1436step1 raw1436step1Labels raw1436step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3300 node3300Labels := by rfl

def raw1437 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2]]
def raw1437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1437step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw1437step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1437step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw1437step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1437 raw1437Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw1437 raw1437Labels = mixedMoment B raw1437step0 raw1437step0Labels := by
      have ha : raw1437step0 = (fun i j => raw1437 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1437step0 raw1437; decide +kernel
      have hl : raw1437step0Labels = raw1437Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1437 raw1437Labels permutation8 permutation4
    mixedMoment B raw1437step0 raw1437step0Labels = mixedMoment B raw1437step1 raw1437step1Labels := by
      have ha : raw1437step1 = raw1437step0 := by apply Matrix.ext; unfold raw1437step1 raw1437step0; decide +kernel
      have hl : raw1437step0Labels = labelEmbedding7 ∘ raw1437step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1437step0 raw1437step0Labels raw1437step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw1438 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2]]
def raw1438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1438step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw1438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1438 raw1438Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw1438 raw1438Labels = mixedMoment B raw1438step0 raw1438step0Labels := by
      have ha : raw1438step0 = (fun i j => raw1438 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1438step0 raw1438; decide +kernel
      have hl : raw1438step0Labels = raw1438Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1438 raw1438Labels permutation8 permutation4
    _ = mixedMoment B node1246 node1246Labels := by rfl

def raw1439 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2]]
def raw1439Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1439step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw1439step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1439step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1439step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1439step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1439step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1439 raw1439Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw1439 raw1439Labels = mixedMoment B raw1439step0 raw1439step0Labels := by
      have ha : raw1439step0 = (fun i j => raw1439 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1439step0 raw1439; decide +kernel
      have hl : raw1439step0Labels = raw1439Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1439 raw1439Labels permutation8 permutation6
    mixedMoment B raw1439step0 raw1439step0Labels = mixedMoment B raw1439step1 raw1439step1Labels := by
      have ha : raw1439step1 = -raw1439step0 := by apply Matrix.ext; change ∀ i j, raw1439step1 i j = -(raw1439step0 i j); unfold raw1439step1 raw1439step0; decide +kernel
      have hl : raw1439step1Labels = raw1439step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1439step1 raw1439step1Labels = mixedMoment B raw1439step2 raw1439step2Labels := by
      have ha : raw1439step2 = raw1439step1 := by apply Matrix.ext; unfold raw1439step2 raw1439step1; decide +kernel
      have hl : raw1439step1Labels = labelEmbedding1 ∘ raw1439step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1439step1 raw1439step1Labels raw1439step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3301 node3301Labels := by rfl

def raw1440 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1440step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1440step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1440 raw1440Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw1440 raw1440Labels = mixedMoment B raw1440step0 raw1440step0Labels := by
      have ha : raw1440step0 = (fun i j => raw1440 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1440step0 raw1440; decide +kernel
      have hl : raw1440step0Labels = raw1440Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1440 raw1440Labels permutation32 permutation4
    mixedMoment B raw1440step0 raw1440step0Labels = mixedMoment B raw1440step1 raw1440step1Labels := by
      have ha : raw1440step1 = raw1440step0 := by apply Matrix.ext; unfold raw1440step1 raw1440step0; decide +kernel
      have hl : raw1440step0Labels = labelEmbedding7 ∘ raw1440step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1440step0 raw1440step0Labels raw1440step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4618 node4618Labels := by rfl

def raw1441 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1441 raw1441Labels = mixedMoment B node1293 node1293Labels := by
  calc
    mixedMoment B raw1441 raw1441Labels = mixedMoment B raw1441step0 raw1441step0Labels := by
      have ha : raw1441step0 = (fun i j => raw1441 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1441step0 raw1441; decide +kernel
      have hl : raw1441step0Labels = raw1441Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1441 raw1441Labels permutation32 permutation4
    _ = mixedMoment B node1293 node1293Labels := by rfl

def raw1442 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1442Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1442step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1442step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1442step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1442 raw1442Labels = mixedMoment B node3304 node3304Labels := by
  calc
    mixedMoment B raw1442 raw1442Labels = mixedMoment B raw1442step0 raw1442step0Labels := by
      have ha : raw1442step0 = (fun i j => raw1442 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1442step0 raw1442; decide +kernel
      have hl : raw1442step0Labels = raw1442Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1442 raw1442Labels permutation32 permutation6
    mixedMoment B raw1442step0 raw1442step0Labels = mixedMoment B raw1442step1 raw1442step1Labels := by
      have ha : raw1442step1 = -raw1442step0 := by apply Matrix.ext; change ∀ i j, raw1442step1 i j = -(raw1442step0 i j); unfold raw1442step1 raw1442step0; decide +kernel
      have hl : raw1442step1Labels = raw1442step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1442step1 raw1442step1Labels = mixedMoment B raw1442step2 raw1442step2Labels := by
      have ha : raw1442step2 = raw1442step1 := by apply Matrix.ext; unfold raw1442step2 raw1442step1; decide +kernel
      have hl : raw1442step1Labels = labelEmbedding1 ∘ raw1442step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1442step1 raw1442step1Labels raw1442step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3304 node3304Labels := by rfl

def raw1443 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1443step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1443step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1443step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1443step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1443 raw1443Labels = mixedMoment B node4619 node4619Labels := by
  calc
    mixedMoment B raw1443 raw1443Labels = mixedMoment B raw1443step0 raw1443step0Labels := by
      have ha : raw1443step0 = (fun i j => raw1443 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1443step0 raw1443; decide +kernel
      have hl : raw1443step0Labels = raw1443Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1443 raw1443Labels permutation8 permutation4
    mixedMoment B raw1443step0 raw1443step0Labels = mixedMoment B raw1443step1 raw1443step1Labels := by
      have ha : raw1443step1 = raw1443step0 := by apply Matrix.ext; unfold raw1443step1 raw1443step0; decide +kernel
      have hl : raw1443step0Labels = labelEmbedding7 ∘ raw1443step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1443step0 raw1443step0Labels raw1443step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4619 node4619Labels := by rfl

def raw1444 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1444step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw1444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1444 raw1444Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw1444 raw1444Labels = mixedMoment B raw1444step0 raw1444step0Labels := by
      have ha : raw1444step0 = (fun i j => raw1444 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1444step0 raw1444; decide +kernel
      have hl : raw1444step0Labels = raw1444Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1444 raw1444Labels permutation8 permutation4
    _ = mixedMoment B node1294 node1294Labels := by rfl

def raw1445 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2]]
def raw1445Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1445step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1445step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1445step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1445step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1445step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1445 raw1445Labels = mixedMoment B node3305 node3305Labels := by
  calc
    mixedMoment B raw1445 raw1445Labels = mixedMoment B raw1445step0 raw1445step0Labels := by
      have ha : raw1445step0 = (fun i j => raw1445 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1445step0 raw1445; decide +kernel
      have hl : raw1445step0Labels = raw1445Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1445 raw1445Labels permutation8 permutation6
    mixedMoment B raw1445step0 raw1445step0Labels = mixedMoment B raw1445step1 raw1445step1Labels := by
      have ha : raw1445step1 = -raw1445step0 := by apply Matrix.ext; change ∀ i j, raw1445step1 i j = -(raw1445step0 i j); unfold raw1445step1 raw1445step0; decide +kernel
      have hl : raw1445step1Labels = raw1445step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1445step1 raw1445step1Labels = mixedMoment B raw1445step2 raw1445step2Labels := by
      have ha : raw1445step2 = raw1445step1 := by apply Matrix.ext; unfold raw1445step2 raw1445step1; decide +kernel
      have hl : raw1445step1Labels = labelEmbedding1 ∘ raw1445step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1445step1 raw1445step1Labels raw1445step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3305 node3305Labels := by rfl

def raw1446 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 1, 1], ![0, 3, -3]]
def raw1446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1446step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw1446step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1446step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw1446step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1446 raw1446Labels = mixedMoment B node4621 node4621Labels := by
  calc
    mixedMoment B raw1446 raw1446Labels = mixedMoment B raw1446step0 raw1446step0Labels := by
      have ha : raw1446step0 = (fun i j => raw1446 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1446step0 raw1446; decide +kernel
      have hl : raw1446step0Labels = raw1446Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1446 raw1446Labels permutation2 permutation4
    mixedMoment B raw1446step0 raw1446step0Labels = mixedMoment B raw1446step1 raw1446step1Labels := by
      have ha : raw1446step1 = raw1446step0 := by apply Matrix.ext; unfold raw1446step1 raw1446step0; decide +kernel
      have hl : raw1446step0Labels = labelEmbedding7 ∘ raw1446step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1446step0 raw1446step0Labels raw1446step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4621 node4621Labels := by rfl

def raw1447 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 1, 1], ![0, 3, -3]]
def raw1447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1447step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw1447step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1447 raw1447Labels = mixedMoment B node1297 node1297Labels := by
  calc
    mixedMoment B raw1447 raw1447Labels = mixedMoment B raw1447step0 raw1447step0Labels := by
      have ha : raw1447step0 = (fun i j => raw1447 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1447step0 raw1447; decide +kernel
      have hl : raw1447step0Labels = raw1447Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1447 raw1447Labels permutation2 permutation4
    _ = mixedMoment B node1297 node1297Labels := by rfl

def raw1448 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 1, 1], ![0, 3, -3]]
def raw1448Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1448step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def raw1448step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1448step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![2, 2, -4]]
def raw1448step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1448 raw1448Labels = mixedMoment B node2289 node2289Labels := by
  calc
    mixedMoment B raw1448 raw1448Labels = mixedMoment B raw1448step0 raw1448step0Labels := by
      have ha : raw1448step0 = (fun i j => raw1448 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1448step0 raw1448; decide +kernel
      have hl : raw1448step0Labels = raw1448Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1448 raw1448Labels permutation7 permutation6
    mixedMoment B raw1448step0 raw1448step0Labels = mixedMoment B raw1448step1 raw1448step1Labels := by
      have ha : raw1448step1 = raw1448step0 := by apply Matrix.ext; unfold raw1448step1 raw1448step0; decide +kernel
      have hl : raw1448step0Labels = labelEmbedding1 ∘ raw1448step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1448step0 raw1448step0Labels raw1448step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2289 node2289Labels := by rfl

def raw1449 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw1449Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1449step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1449step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1449 raw1449Labels = mixedMoment B node4622 node4622Labels := by
  calc
    mixedMoment B raw1449 raw1449Labels = mixedMoment B raw1449step0 raw1449step0Labels := by
      have ha : raw1449step0 = (fun i j => raw1449 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1449step0 raw1449; decide +kernel
      have hl : raw1449step0Labels = raw1449Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1449 raw1449Labels permutation32 permutation4
    mixedMoment B raw1449step0 raw1449step0Labels = mixedMoment B raw1449step1 raw1449step1Labels := by
      have ha : raw1449step1 = raw1449step0 := by apply Matrix.ext; unfold raw1449step1 raw1449step0; decide +kernel
      have hl : raw1449step0Labels = labelEmbedding7 ∘ raw1449step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1449step0 raw1449step0Labels raw1449step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4622 node4622Labels := by rfl

def raw1450 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw1450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw1450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1450 raw1450Labels = mixedMoment B node1299 node1299Labels := by
  calc
    mixedMoment B raw1450 raw1450Labels = mixedMoment B raw1450step0 raw1450step0Labels := by
      have ha : raw1450step0 = (fun i j => raw1450 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1450step0 raw1450; decide +kernel
      have hl : raw1450step0Labels = raw1450Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1450 raw1450Labels permutation32 permutation4
    _ = mixedMoment B node1299 node1299Labels := by rfl

def raw1451 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1]]
def raw1451Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1451step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1451step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1451step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1451 raw1451Labels = mixedMoment B node3307 node3307Labels := by
  calc
    mixedMoment B raw1451 raw1451Labels = mixedMoment B raw1451step0 raw1451step0Labels := by
      have ha : raw1451step0 = (fun i j => raw1451 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1451step0 raw1451; decide +kernel
      have hl : raw1451step0Labels = raw1451Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1451 raw1451Labels permutation48 permutation3
    mixedMoment B raw1451step0 raw1451step0Labels = mixedMoment B raw1451step1 raw1451step1Labels := by
      have ha : raw1451step1 = -raw1451step0 := by apply Matrix.ext; change ∀ i j, raw1451step1 i j = -(raw1451step0 i j); unfold raw1451step1 raw1451step0; decide +kernel
      have hl : raw1451step1Labels = raw1451step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1451step1 raw1451step1Labels = mixedMoment B raw1451step2 raw1451step2Labels := by
      have ha : raw1451step2 = raw1451step1 := by apply Matrix.ext; unfold raw1451step2 raw1451step1; decide +kernel
      have hl : raw1451step1Labels = labelEmbedding1 ∘ raw1451step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1451step1 raw1451step1Labels raw1451step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3307 node3307Labels := by rfl

def raw1452 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1452Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1452step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1452step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1452step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1452 raw1452Labels = mixedMoment B node4623 node4623Labels := by
  calc
    mixedMoment B raw1452 raw1452Labels = mixedMoment B raw1452step0 raw1452step0Labels := by
      have ha : raw1452step0 = (fun i j => raw1452 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1452step0 raw1452; decide +kernel
      have hl : raw1452step0Labels = raw1452Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1452 raw1452Labels permutation8 permutation4
    mixedMoment B raw1452step0 raw1452step0Labels = mixedMoment B raw1452step1 raw1452step1Labels := by
      have ha : raw1452step1 = raw1452step0 := by apply Matrix.ext; unfold raw1452step1 raw1452step0; decide +kernel
      have hl : raw1452step0Labels = labelEmbedding7 ∘ raw1452step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1452step0 raw1452step0Labels raw1452step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4623 node4623Labels := by rfl

def raw1453 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1453step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw1453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1453 raw1453Labels = mixedMoment B node1300 node1300Labels := by
  calc
    mixedMoment B raw1453 raw1453Labels = mixedMoment B raw1453step0 raw1453step0Labels := by
      have ha : raw1453step0 = (fun i j => raw1453 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1453step0 raw1453; decide +kernel
      have hl : raw1453step0Labels = raw1453Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1453 raw1453Labels permutation8 permutation4
    _ = mixedMoment B node1300 node1300Labels := by rfl

def raw1454 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 2, -2]]
def raw1454Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1454step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw1454step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw1454step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1454step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw1454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1454 raw1454Labels = mixedMoment B node3308 node3308Labels := by
  calc
    mixedMoment B raw1454 raw1454Labels = mixedMoment B raw1454step0 raw1454step0Labels := by
      have ha : raw1454step0 = (fun i j => raw1454 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1454step0 raw1454; decide +kernel
      have hl : raw1454step0Labels = raw1454Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1454 raw1454Labels permutation8 permutation6
    mixedMoment B raw1454step0 raw1454step0Labels = mixedMoment B raw1454step1 raw1454step1Labels := by
      have ha : raw1454step1 = -raw1454step0 := by apply Matrix.ext; change ∀ i j, raw1454step1 i j = -(raw1454step0 i j); unfold raw1454step1 raw1454step0; decide +kernel
      have hl : raw1454step1Labels = raw1454step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1454step1 raw1454step1Labels = mixedMoment B raw1454step2 raw1454step2Labels := by
      have ha : raw1454step2 = raw1454step1 := by apply Matrix.ext; unfold raw1454step2 raw1454step1; decide +kernel
      have hl : raw1454step1Labels = labelEmbedding1 ∘ raw1454step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1454step1 raw1454step1Labels raw1454step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3308 node3308Labels := by rfl

def raw1455 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1455Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1455step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1455step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1455step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1455 raw1455Labels = mixedMoment B node4624 node4624Labels := by
  calc
    mixedMoment B raw1455 raw1455Labels = mixedMoment B raw1455step0 raw1455step0Labels := by
      have ha : raw1455step0 = (fun i j => raw1455 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1455step0 raw1455; decide +kernel
      have hl : raw1455step0Labels = raw1455Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1455 raw1455Labels permutation8 permutation4
    mixedMoment B raw1455step0 raw1455step0Labels = mixedMoment B raw1455step1 raw1455step1Labels := by
      have ha : raw1455step1 = raw1455step0 := by apply Matrix.ext; unfold raw1455step1 raw1455step0; decide +kernel
      have hl : raw1455step0Labels = labelEmbedding7 ∘ raw1455step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1455step0 raw1455step0Labels raw1455step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4624 node4624Labels := by rfl

def raw1456 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1456step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw1456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1456 raw1456Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw1456 raw1456Labels = mixedMoment B raw1456step0 raw1456step0Labels := by
      have ha : raw1456step0 = (fun i j => raw1456 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1456step0 raw1456; decide +kernel
      have hl : raw1456step0Labels = raw1456Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1456 raw1456Labels permutation8 permutation4
    _ = mixedMoment B node1301 node1301Labels := by rfl

def raw1457 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 2, -1]]
def raw1457Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1457step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw1457step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1457step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1457step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1457step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1457step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1457 raw1457Labels = mixedMoment B node3309 node3309Labels := by
  calc
    mixedMoment B raw1457 raw1457Labels = mixedMoment B raw1457step0 raw1457step0Labels := by
      have ha : raw1457step0 = (fun i j => raw1457 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1457step0 raw1457; decide +kernel
      have hl : raw1457step0Labels = raw1457Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1457 raw1457Labels permutation10 permutation3
    mixedMoment B raw1457step0 raw1457step0Labels = mixedMoment B raw1457step1 raw1457step1Labels := by
      have ha : raw1457step1 = -raw1457step0 := by apply Matrix.ext; change ∀ i j, raw1457step1 i j = -(raw1457step0 i j); unfold raw1457step1 raw1457step0; decide +kernel
      have hl : raw1457step1Labels = raw1457step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1457step1 raw1457step1Labels = mixedMoment B raw1457step2 raw1457step2Labels := by
      have ha : raw1457step2 = raw1457step1 := by apply Matrix.ext; unfold raw1457step2 raw1457step1; decide +kernel
      have hl : raw1457step1Labels = labelEmbedding1 ∘ raw1457step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1457step1 raw1457step1Labels raw1457step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3309 node3309Labels := by rfl

def raw1458 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 3, -2]]
def raw1458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1458step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw1458step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1458step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw1458step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1458 raw1458Labels = mixedMoment B node4625 node4625Labels := by
  calc
    mixedMoment B raw1458 raw1458Labels = mixedMoment B raw1458step0 raw1458step0Labels := by
      have ha : raw1458step0 = (fun i j => raw1458 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1458step0 raw1458; decide +kernel
      have hl : raw1458step0Labels = raw1458Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1458 raw1458Labels permutation2 permutation4
    mixedMoment B raw1458step0 raw1458step0Labels = mixedMoment B raw1458step1 raw1458step1Labels := by
      have ha : raw1458step1 = raw1458step0 := by apply Matrix.ext; unfold raw1458step1 raw1458step0; decide +kernel
      have hl : raw1458step0Labels = labelEmbedding7 ∘ raw1458step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1458step0 raw1458step0Labels raw1458step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4625 node4625Labels := by rfl

def raw1459 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 3, -2]]
def raw1459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1459step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw1459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1459 raw1459Labels = mixedMoment B node1304 node1304Labels := by
  calc
    mixedMoment B raw1459 raw1459Labels = mixedMoment B raw1459step0 raw1459step0Labels := by
      have ha : raw1459step0 = (fun i j => raw1459 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1459step0 raw1459; decide +kernel
      have hl : raw1459step0Labels = raw1459Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1459 raw1459Labels permutation2 permutation4
    _ = mixedMoment B node1304 node1304Labels := by rfl

def raw1460 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 1, 0], ![-1, 3, -2]]
def raw1460Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1460step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, -1, 3]]
def raw1460step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1460step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![2, 1, -3]]
def raw1460step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1460step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![2, 1, -3]]
def raw1460step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1460 raw1460Labels = mixedMoment B node3310 node3310Labels := by
  calc
    mixedMoment B raw1460 raw1460Labels = mixedMoment B raw1460step0 raw1460step0Labels := by
      have ha : raw1460step0 = (fun i j => raw1460 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1460step0 raw1460; decide +kernel
      have hl : raw1460step0Labels = raw1460Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1460 raw1460Labels permutation2 permutation6
    mixedMoment B raw1460step0 raw1460step0Labels = mixedMoment B raw1460step1 raw1460step1Labels := by
      have ha : raw1460step1 = -raw1460step0 := by apply Matrix.ext; change ∀ i j, raw1460step1 i j = -(raw1460step0 i j); unfold raw1460step1 raw1460step0; decide +kernel
      have hl : raw1460step1Labels = raw1460step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1460step1 raw1460step1Labels = mixedMoment B raw1460step2 raw1460step2Labels := by
      have ha : raw1460step2 = raw1460step1 := by apply Matrix.ext; unfold raw1460step2 raw1460step1; decide +kernel
      have hl : raw1460step1Labels = labelEmbedding1 ∘ raw1460step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1460step1 raw1460step1Labels raw1460step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3310 node3310Labels := by rfl

def raw1461 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 2, 0], ![0, 2, -2]]
def raw1461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1461step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw1461step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1461step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw1461step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1461 raw1461Labels = mixedMoment B node4627 node4627Labels := by
  calc
    mixedMoment B raw1461 raw1461Labels = mixedMoment B raw1461step0 raw1461step0Labels := by
      have ha : raw1461step0 = (fun i j => raw1461 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1461step0 raw1461; decide +kernel
      have hl : raw1461step0Labels = raw1461Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1461 raw1461Labels permutation2 permutation4
    mixedMoment B raw1461step0 raw1461step0Labels = mixedMoment B raw1461step1 raw1461step1Labels := by
      have ha : raw1461step1 = raw1461step0 := by apply Matrix.ext; unfold raw1461step1 raw1461step0; decide +kernel
      have hl : raw1461step0Labels = labelEmbedding7 ∘ raw1461step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1461step0 raw1461step0Labels raw1461step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4627 node4627Labels := by rfl

def raw1462 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 2, 0], ![0, 2, -2]]
def raw1462Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1462step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw1462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1462 raw1462Labels = mixedMoment B node1311 node1311Labels := by
  calc
    mixedMoment B raw1462 raw1462Labels = mixedMoment B raw1462step0 raw1462step0Labels := by
      have ha : raw1462step0 = (fun i j => raw1462 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1462step0 raw1462; decide +kernel
      have hl : raw1462step0Labels = raw1462Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1462 raw1462Labels permutation2 permutation4
    _ = mixedMoment B node1311 node1311Labels := by rfl

def raw1463 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 2, 0], ![0, 2, -2]]
def raw1463Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1463step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -2, 2], ![-2, 0, 2]]
def raw1463step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1463step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]
def raw1463step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1463step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 2, -2], ![2, 0, -2]]
def raw1463step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1463 raw1463Labels = mixedMoment B node3311 node3311Labels := by
  calc
    mixedMoment B raw1463 raw1463Labels = mixedMoment B raw1463step0 raw1463step0Labels := by
      have ha : raw1463step0 = (fun i j => raw1463 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1463step0 raw1463; decide +kernel
      have hl : raw1463step0Labels = raw1463Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1463 raw1463Labels permutation3 permutation3
    mixedMoment B raw1463step0 raw1463step0Labels = mixedMoment B raw1463step1 raw1463step1Labels := by
      have ha : raw1463step1 = -raw1463step0 := by apply Matrix.ext; change ∀ i j, raw1463step1 i j = -(raw1463step0 i j); unfold raw1463step1 raw1463step0; decide +kernel
      have hl : raw1463step1Labels = raw1463step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1463step1 raw1463step1Labels = mixedMoment B raw1463step2 raw1463step2Labels := by
      have ha : raw1463step2 = raw1463step1 := by apply Matrix.ext; unfold raw1463step2 raw1463step1; decide +kernel
      have hl : raw1463step1Labels = labelEmbedding1 ∘ raw1463step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1463step1 raw1463step1Labels raw1463step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3311 node3311Labels := by rfl

def raw1464 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1464step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw1464step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1464step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw1464step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1464 raw1464Labels = mixedMoment B node4628 node4628Labels := by
  calc
    mixedMoment B raw1464 raw1464Labels = mixedMoment B raw1464step0 raw1464step0Labels := by
      have ha : raw1464step0 = (fun i j => raw1464 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1464step0 raw1464; decide +kernel
      have hl : raw1464step0Labels = raw1464Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1464 raw1464Labels permutation2 permutation4
    mixedMoment B raw1464step0 raw1464step0Labels = mixedMoment B raw1464step1 raw1464step1Labels := by
      have ha : raw1464step1 = raw1464step0 := by apply Matrix.ext; unfold raw1464step1 raw1464step0; decide +kernel
      have hl : raw1464step0Labels = labelEmbedding7 ∘ raw1464step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1464step0 raw1464step0Labels raw1464step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4628 node4628Labels := by rfl

def raw1465 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1465Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1465step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw1465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1465 raw1465Labels = mixedMoment B node1312 node1312Labels := by
  calc
    mixedMoment B raw1465 raw1465Labels = mixedMoment B raw1465step0 raw1465step0Labels := by
      have ha : raw1465step0 = (fun i j => raw1465 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1465step0 raw1465; decide +kernel
      have hl : raw1465step0Labels = raw1465Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1465 raw1465Labels permutation2 permutation4
    _ = mixedMoment B node1312 node1312Labels := by rfl

def raw1466 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -4, 2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1466Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1466step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, -1, 2], ![-1, -1, 2]]
def raw1466step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1466step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]
def raw1466step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1466step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![1, 1, -2], ![1, 1, -2]]
def raw1466step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1466 raw1466Labels = mixedMoment B node3312 node3312Labels := by
  calc
    mixedMoment B raw1466 raw1466Labels = mixedMoment B raw1466step0 raw1466step0Labels := by
      have ha : raw1466step0 = (fun i j => raw1466 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1466step0 raw1466; decide +kernel
      have hl : raw1466step0Labels = raw1466Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1466 raw1466Labels permutation2 permutation3
    mixedMoment B raw1466step0 raw1466step0Labels = mixedMoment B raw1466step1 raw1466step1Labels := by
      have ha : raw1466step1 = -raw1466step0 := by apply Matrix.ext; change ∀ i j, raw1466step1 i j = -(raw1466step0 i j); unfold raw1466step1 raw1466step0; decide +kernel
      have hl : raw1466step1Labels = raw1466step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1466step1 raw1466step1Labels = mixedMoment B raw1466step2 raw1466step2Labels := by
      have ha : raw1466step2 = raw1466step1 := by apply Matrix.ext; unfold raw1466step2 raw1466step1; decide +kernel
      have hl : raw1466step1Labels = labelEmbedding1 ∘ raw1466step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1466step1 raw1466step1Labels raw1466step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3312 node3312Labels := by rfl

def raw1467 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 4, -2]]
def raw1467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1467step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw1467step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1467step1 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw1467step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1467 raw1467Labels = mixedMoment B node4629 node4629Labels := by
  calc
    mixedMoment B raw1467 raw1467Labels = mixedMoment B raw1467step0 raw1467step0Labels := by
      have ha : raw1467step0 = (fun i j => raw1467 (permutation0 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1467step0 raw1467; decide +kernel
      have hl : raw1467step0Labels = raw1467Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1467 raw1467Labels permutation0 permutation4
    mixedMoment B raw1467step0 raw1467step0Labels = mixedMoment B raw1467step1 raw1467step1Labels := by
      have ha : raw1467step1 = raw1467step0 := by apply Matrix.ext; unfold raw1467step1 raw1467step0; decide +kernel
      have hl : raw1467step0Labels = labelEmbedding7 ∘ raw1467step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1467step0 raw1467step0Labels raw1467step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4629 node4629Labels := by rfl

def raw1468 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 4, -2]]
def raw1468Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1468step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw1468step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1468 raw1468Labels = mixedMoment B node1313 node1313Labels := by
  calc
    mixedMoment B raw1468 raw1468Labels = mixedMoment B raw1468step0 raw1468step0Labels := by
      have ha : raw1468step0 = (fun i j => raw1468 (permutation0 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1468step0 raw1468; decide +kernel
      have hl : raw1468step0Labels = raw1468Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1468 raw1468Labels permutation0 permutation4
    _ = mixedMoment B node1313 node1313Labels := by rfl

def raw1469 : Matrix (Fin 2) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 4, -2]]
def raw1469Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1469step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, -2, 4], ![2, 2, -4]]
def raw1469step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1469step1 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, -2, 4], ![2, 2, -4]]
def raw1469step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1469 raw1469Labels = mixedMoment B node3313 node3313Labels := by
  calc
    mixedMoment B raw1469 raw1469Labels = mixedMoment B raw1469step0 raw1469step0Labels := by
      have ha : raw1469step0 = (fun i j => raw1469 (permutation1 i) (permutation3 j)) := by apply Matrix.ext; unfold raw1469step0 raw1469; decide +kernel
      have hl : raw1469step0Labels = raw1469Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1469 raw1469Labels permutation1 permutation3
    mixedMoment B raw1469step0 raw1469step0Labels = mixedMoment B raw1469step1 raw1469step1Labels := by
      have ha : raw1469step1 = raw1469step0 := by apply Matrix.ext; unfold raw1469step1 raw1469step0; decide +kernel
      have hl : raw1469step0Labels = labelEmbedding1 ∘ raw1469step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1469step0 raw1469step0Labels raw1469step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3313 node3313Labels := by rfl

def raw1470 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1470step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1470step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1470step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1470 raw1470Labels = mixedMoment B node4630 node4630Labels := by
  calc
    mixedMoment B raw1470 raw1470Labels = mixedMoment B raw1470step0 raw1470step0Labels := by
      have ha : raw1470step0 = (fun i j => raw1470 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1470step0 raw1470; decide +kernel
      have hl : raw1470step0Labels = raw1470Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1470 raw1470Labels permutation152 permutation4
    mixedMoment B raw1470step0 raw1470step0Labels = mixedMoment B raw1470step1 raw1470step1Labels := by
      have ha : raw1470step1 = raw1470step0 := by apply Matrix.ext; unfold raw1470step1 raw1470step0; decide +kernel
      have hl : raw1470step0Labels = labelEmbedding7 ∘ raw1470step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1470step0 raw1470step0Labels raw1470step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4630 node4630Labels := by rfl

def raw1471 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1471Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1471step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1471 raw1471Labels = mixedMoment B node1759 node1759Labels := by
  calc
    mixedMoment B raw1471 raw1471Labels = mixedMoment B raw1471step0 raw1471step0Labels := by
      have ha : raw1471step0 = (fun i j => raw1471 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1471step0 raw1471; decide +kernel
      have hl : raw1471step0Labels = raw1471Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1471 raw1471Labels permutation152 permutation4
    _ = mixedMoment B node1759 node1759Labels := by rfl

def raw1472 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1472Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw1472step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1472step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1472step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1472step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw1472step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1472 raw1472Labels = mixedMoment B node1833 node1833Labels := by
  calc
    mixedMoment B raw1472 raw1472Labels = mixedMoment B raw1472step0 raw1472step0Labels := by
      have ha : raw1472step0 = (fun i j => raw1472 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1472step0 raw1472; decide +kernel
      have hl : raw1472step0Labels = raw1472Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1472 raw1472Labels permutation160 permutation6
    mixedMoment B raw1472step0 raw1472step0Labels = mixedMoment B raw1472step1 raw1472step1Labels := by
      have ha : raw1472step1 = -raw1472step0 := by apply Matrix.ext; change ∀ i j, raw1472step1 i j = -(raw1472step0 i j); unfold raw1472step1 raw1472step0; decide +kernel
      have hl : raw1472step1Labels = raw1472step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1472step1 raw1472step1Labels = mixedMoment B raw1472step2 raw1472step2Labels := by
      have ha : raw1472step2 = raw1472step1 := by apply Matrix.ext; unfold raw1472step2 raw1472step1; decide +kernel
      have hl : raw1472step1Labels = labelEmbedding1 ∘ raw1472step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1472step1 raw1472step1Labels raw1472step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1833 node1833Labels := by rfl

def raw1473 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1473step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1473step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1473step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1473 raw1473Labels = mixedMoment B node4631 node4631Labels := by
  calc
    mixedMoment B raw1473 raw1473Labels = mixedMoment B raw1473step0 raw1473step0Labels := by
      have ha : raw1473step0 = (fun i j => raw1473 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1473step0 raw1473; decide +kernel
      have hl : raw1473step0Labels = raw1473Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1473 raw1473Labels permutation152 permutation4
    mixedMoment B raw1473step0 raw1473step0Labels = mixedMoment B raw1473step1 raw1473step1Labels := by
      have ha : raw1473step1 = raw1473step0 := by apply Matrix.ext; unfold raw1473step1 raw1473step0; decide +kernel
      have hl : raw1473step0Labels = labelEmbedding7 ∘ raw1473step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1473step0 raw1473step0Labels raw1473step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4631 node4631Labels := by rfl

def raw1474 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1474step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1474 raw1474Labels = mixedMoment B node1760 node1760Labels := by
  calc
    mixedMoment B raw1474 raw1474Labels = mixedMoment B raw1474step0 raw1474step0Labels := by
      have ha : raw1474step0 = (fun i j => raw1474 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1474step0 raw1474; decide +kernel
      have hl : raw1474step0Labels = raw1474Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1474 raw1474Labels permutation152 permutation4
    _ = mixedMoment B node1760 node1760Labels := by rfl

def raw1475 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1475Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw1475step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1475step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1475step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1475step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1475step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1475 raw1475Labels = mixedMoment B node1836 node1836Labels := by
  calc
    mixedMoment B raw1475 raw1475Labels = mixedMoment B raw1475step0 raw1475step0Labels := by
      have ha : raw1475step0 = (fun i j => raw1475 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1475step0 raw1475; decide +kernel
      have hl : raw1475step0Labels = raw1475Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1475 raw1475Labels permutation158 permutation6
    mixedMoment B raw1475step0 raw1475step0Labels = mixedMoment B raw1475step1 raw1475step1Labels := by
      have ha : raw1475step1 = -raw1475step0 := by apply Matrix.ext; change ∀ i j, raw1475step1 i j = -(raw1475step0 i j); unfold raw1475step1 raw1475step0; decide +kernel
      have hl : raw1475step1Labels = raw1475step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1475step1 raw1475step1Labels = mixedMoment B raw1475step2 raw1475step2Labels := by
      have ha : raw1475step2 = raw1475step1 := by apply Matrix.ext; unfold raw1475step2 raw1475step1; decide +kernel
      have hl : raw1475step1Labels = labelEmbedding1 ∘ raw1475step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1475step1 raw1475step1Labels raw1475step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1836 node1836Labels := by rfl

def raw1476 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1476step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1476step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1476 raw1476Labels = mixedMoment B node4632 node4632Labels := by
  calc
    mixedMoment B raw1476 raw1476Labels = mixedMoment B raw1476step0 raw1476step0Labels := by
      have ha : raw1476step0 = (fun i j => raw1476 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1476step0 raw1476; decide +kernel
      have hl : raw1476step0Labels = raw1476Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1476 raw1476Labels permutation152 permutation4
    mixedMoment B raw1476step0 raw1476step0Labels = mixedMoment B raw1476step1 raw1476step1Labels := by
      have ha : raw1476step1 = raw1476step0 := by apply Matrix.ext; unfold raw1476step1 raw1476step0; decide +kernel
      have hl : raw1476step0Labels = labelEmbedding7 ∘ raw1476step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1476step0 raw1476step0Labels raw1476step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4632 node4632Labels := by rfl

def raw1477 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1477Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1477step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1477 raw1477Labels = mixedMoment B node1761 node1761Labels := by
  calc
    mixedMoment B raw1477 raw1477Labels = mixedMoment B raw1477step0 raw1477step0Labels := by
      have ha : raw1477step0 = (fun i j => raw1477 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1477step0 raw1477; decide +kernel
      have hl : raw1477step0Labels = raw1477Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1477 raw1477Labels permutation152 permutation4
    _ = mixedMoment B node1761 node1761Labels := by rfl

def raw1478 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1478Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw1478step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1478step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1478step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1478step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1478step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1478 raw1478Labels = mixedMoment B node1837 node1837Labels := by
  calc
    mixedMoment B raw1478 raw1478Labels = mixedMoment B raw1478step0 raw1478step0Labels := by
      have ha : raw1478step0 = (fun i j => raw1478 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1478step0 raw1478; decide +kernel
      have hl : raw1478step0Labels = raw1478Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1478 raw1478Labels permutation158 permutation6
    mixedMoment B raw1478step0 raw1478step0Labels = mixedMoment B raw1478step1 raw1478step1Labels := by
      have ha : raw1478step1 = -raw1478step0 := by apply Matrix.ext; change ∀ i j, raw1478step1 i j = -(raw1478step0 i j); unfold raw1478step1 raw1478step0; decide +kernel
      have hl : raw1478step1Labels = raw1478step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1478step1 raw1478step1Labels = mixedMoment B raw1478step2 raw1478step2Labels := by
      have ha : raw1478step2 = raw1478step1 := by apply Matrix.ext; unfold raw1478step2 raw1478step1; decide +kernel
      have hl : raw1478step1Labels = labelEmbedding1 ∘ raw1478step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1478step1 raw1478step1Labels raw1478step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1837 node1837Labels := by rfl

def raw1479 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1479step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1479step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1479 raw1479Labels = mixedMoment B node4633 node4633Labels := by
  calc
    mixedMoment B raw1479 raw1479Labels = mixedMoment B raw1479step0 raw1479step0Labels := by
      have ha : raw1479step0 = (fun i j => raw1479 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1479step0 raw1479; decide +kernel
      have hl : raw1479step0Labels = raw1479Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1479 raw1479Labels permutation152 permutation4
    mixedMoment B raw1479step0 raw1479step0Labels = mixedMoment B raw1479step1 raw1479step1Labels := by
      have ha : raw1479step1 = raw1479step0 := by apply Matrix.ext; unfold raw1479step1 raw1479step0; decide +kernel
      have hl : raw1479step0Labels = labelEmbedding7 ∘ raw1479step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1479step0 raw1479step0Labels raw1479step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4633 node4633Labels := by rfl

def raw1480 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1480Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1480step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1480 raw1480Labels = mixedMoment B node1762 node1762Labels := by
  calc
    mixedMoment B raw1480 raw1480Labels = mixedMoment B raw1480step0 raw1480step0Labels := by
      have ha : raw1480step0 = (fun i j => raw1480 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1480step0 raw1480; decide +kernel
      have hl : raw1480step0Labels = raw1480Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1480 raw1480Labels permutation152 permutation4
    _ = mixedMoment B node1762 node1762Labels := by rfl

def raw1481 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1481Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw1481step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1481step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1481step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1481step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1481step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1481 raw1481Labels = mixedMoment B node1847 node1847Labels := by
  calc
    mixedMoment B raw1481 raw1481Labels = mixedMoment B raw1481step0 raw1481step0Labels := by
      have ha : raw1481step0 = (fun i j => raw1481 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1481step0 raw1481; decide +kernel
      have hl : raw1481step0Labels = raw1481Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1481 raw1481Labels permutation152 permutation6
    mixedMoment B raw1481step0 raw1481step0Labels = mixedMoment B raw1481step1 raw1481step1Labels := by
      have ha : raw1481step1 = -raw1481step0 := by apply Matrix.ext; change ∀ i j, raw1481step1 i j = -(raw1481step0 i j); unfold raw1481step1 raw1481step0; decide +kernel
      have hl : raw1481step1Labels = raw1481step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1481step1 raw1481step1Labels = mixedMoment B raw1481step2 raw1481step2Labels := by
      have ha : raw1481step2 = raw1481step1 := by apply Matrix.ext; unfold raw1481step2 raw1481step1; decide +kernel
      have hl : raw1481step1Labels = labelEmbedding1 ∘ raw1481step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1481step1 raw1481step1Labels raw1481step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1847 node1847Labels := by rfl

def raw1482 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1482step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1482step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1482step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1482 raw1482Labels = mixedMoment B node4634 node4634Labels := by
  calc
    mixedMoment B raw1482 raw1482Labels = mixedMoment B raw1482step0 raw1482step0Labels := by
      have ha : raw1482step0 = (fun i j => raw1482 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1482step0 raw1482; decide +kernel
      have hl : raw1482step0Labels = raw1482Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1482 raw1482Labels permutation152 permutation4
    mixedMoment B raw1482step0 raw1482step0Labels = mixedMoment B raw1482step1 raw1482step1Labels := by
      have ha : raw1482step1 = raw1482step0 := by apply Matrix.ext; unfold raw1482step1 raw1482step0; decide +kernel
      have hl : raw1482step0Labels = labelEmbedding7 ∘ raw1482step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1482step0 raw1482step0Labels raw1482step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4634 node4634Labels := by rfl

def raw1483 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1483Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1483step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1483 raw1483Labels = mixedMoment B node1763 node1763Labels := by
  calc
    mixedMoment B raw1483 raw1483Labels = mixedMoment B raw1483step0 raw1483step0Labels := by
      have ha : raw1483step0 = (fun i j => raw1483 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1483step0 raw1483; decide +kernel
      have hl : raw1483step0Labels = raw1483Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1483 raw1483Labels permutation152 permutation4
    _ = mixedMoment B node1763 node1763Labels := by rfl

def raw1484 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1484Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw1484step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1484step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1484step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1484step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1484 raw1484Labels = mixedMoment B node1842 node1842Labels := by
  calc
    mixedMoment B raw1484 raw1484Labels = mixedMoment B raw1484step0 raw1484step0Labels := by
      have ha : raw1484step0 = (fun i j => raw1484 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1484step0 raw1484; decide +kernel
      have hl : raw1484step0Labels = raw1484Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1484 raw1484Labels permutation164 permutation6
    mixedMoment B raw1484step0 raw1484step0Labels = mixedMoment B raw1484step1 raw1484step1Labels := by
      have ha : raw1484step1 = -raw1484step0 := by apply Matrix.ext; change ∀ i j, raw1484step1 i j = -(raw1484step0 i j); unfold raw1484step1 raw1484step0; decide +kernel
      have hl : raw1484step1Labels = raw1484step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1484step1 raw1484step1Labels = mixedMoment B raw1484step2 raw1484step2Labels := by
      have ha : raw1484step2 = raw1484step1 := by apply Matrix.ext; unfold raw1484step2 raw1484step1; decide +kernel
      have hl : raw1484step1Labels = labelEmbedding1 ∘ raw1484step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1484step1 raw1484step1Labels raw1484step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1842 node1842Labels := by rfl

def raw1485 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1485step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1485step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1485step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1485 raw1485Labels = mixedMoment B node4635 node4635Labels := by
  calc
    mixedMoment B raw1485 raw1485Labels = mixedMoment B raw1485step0 raw1485step0Labels := by
      have ha : raw1485step0 = (fun i j => raw1485 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1485step0 raw1485; decide +kernel
      have hl : raw1485step0Labels = raw1485Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1485 raw1485Labels permutation152 permutation4
    mixedMoment B raw1485step0 raw1485step0Labels = mixedMoment B raw1485step1 raw1485step1Labels := by
      have ha : raw1485step1 = raw1485step0 := by apply Matrix.ext; unfold raw1485step1 raw1485step0; decide +kernel
      have hl : raw1485step0Labels = labelEmbedding7 ∘ raw1485step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1485step0 raw1485step0Labels raw1485step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4635 node4635Labels := by rfl

def raw1486 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1486Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1486step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1486 raw1486Labels = mixedMoment B node1764 node1764Labels := by
  calc
    mixedMoment B raw1486 raw1486Labels = mixedMoment B raw1486step0 raw1486step0Labels := by
      have ha : raw1486step0 = (fun i j => raw1486 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1486step0 raw1486; decide +kernel
      have hl : raw1486step0Labels = raw1486Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1486 raw1486Labels permutation152 permutation4
    _ = mixedMoment B node1764 node1764Labels := by rfl

def raw1487 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1487Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1487step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1487step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1487step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1487step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1487step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1487step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1487 raw1487Labels = mixedMoment B node1848 node1848Labels := by
  calc
    mixedMoment B raw1487 raw1487Labels = mixedMoment B raw1487step0 raw1487step0Labels := by
      have ha : raw1487step0 = (fun i j => raw1487 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1487step0 raw1487; decide +kernel
      have hl : raw1487step0Labels = raw1487Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1487 raw1487Labels permutation152 permutation6
    mixedMoment B raw1487step0 raw1487step0Labels = mixedMoment B raw1487step1 raw1487step1Labels := by
      have ha : raw1487step1 = -raw1487step0 := by apply Matrix.ext; change ∀ i j, raw1487step1 i j = -(raw1487step0 i j); unfold raw1487step1 raw1487step0; decide +kernel
      have hl : raw1487step1Labels = raw1487step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1487step1 raw1487step1Labels = mixedMoment B raw1487step2 raw1487step2Labels := by
      have ha : raw1487step2 = raw1487step1 := by apply Matrix.ext; unfold raw1487step2 raw1487step1; decide +kernel
      have hl : raw1487step1Labels = labelEmbedding1 ∘ raw1487step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1487step1 raw1487step1Labels raw1487step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1848 node1848Labels := by rfl

def raw1488 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw1488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw1488step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw1488step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1488 raw1488Labels = mixedMoment B node4636 node4636Labels := by
  calc
    mixedMoment B raw1488 raw1488Labels = mixedMoment B raw1488step0 raw1488step0Labels := by
      have ha : raw1488step0 = (fun i j => raw1488 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1488step0 raw1488; decide +kernel
      have hl : raw1488step0Labels = raw1488Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1488 raw1488Labels permutation32 permutation4
    mixedMoment B raw1488step0 raw1488step0Labels = mixedMoment B raw1488step1 raw1488step1Labels := by
      have ha : raw1488step1 = raw1488step0 := by apply Matrix.ext; unfold raw1488step1 raw1488step0; decide +kernel
      have hl : raw1488step0Labels = labelEmbedding7 ∘ raw1488step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1488step0 raw1488step0Labels raw1488step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4636 node4636Labels := by rfl

def raw1489 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw1489Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw1489step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1489 raw1489Labels = mixedMoment B node1765 node1765Labels := by
  calc
    mixedMoment B raw1489 raw1489Labels = mixedMoment B raw1489step0 raw1489step0Labels := by
      have ha : raw1489step0 = (fun i j => raw1489 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1489step0 raw1489; decide +kernel
      have hl : raw1489step0Labels = raw1489Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1489 raw1489Labels permutation32 permutation4
    _ = mixedMoment B node1765 node1765Labels := by rfl

def raw1490 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-2, 2, 0], ![0, 3, -3]]
def raw1490Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-3, 0, 3]]
def raw1490step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw1490step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1490step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw1490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1490 raw1490Labels = mixedMoment B node1843 node1843Labels := by
  calc
    mixedMoment B raw1490 raw1490Labels = mixedMoment B raw1490step0 raw1490step0Labels := by
      have ha : raw1490step0 = (fun i j => raw1490 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1490step0 raw1490; decide +kernel
      have hl : raw1490step0Labels = raw1490Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1490 raw1490Labels permutation34 permutation6
    mixedMoment B raw1490step0 raw1490step0Labels = mixedMoment B raw1490step1 raw1490step1Labels := by
      have ha : raw1490step1 = -raw1490step0 := by apply Matrix.ext; change ∀ i j, raw1490step1 i j = -(raw1490step0 i j); unfold raw1490step1 raw1490step0; decide +kernel
      have hl : raw1490step1Labels = raw1490step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1490step1 raw1490step1Labels = mixedMoment B raw1490step2 raw1490step2Labels := by
      have ha : raw1490step2 = raw1490step1 := by apply Matrix.ext; unfold raw1490step2 raw1490step1; decide +kernel
      have hl : raw1490step1Labels = labelEmbedding1 ∘ raw1490step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1490step1 raw1490step1Labels raw1490step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1843 node1843Labels := by rfl

def raw1491 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1491step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1491step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1491 raw1491Labels = mixedMoment B node4637 node4637Labels := by
  calc
    mixedMoment B raw1491 raw1491Labels = mixedMoment B raw1491step0 raw1491step0Labels := by
      have ha : raw1491step0 = (fun i j => raw1491 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1491step0 raw1491; decide +kernel
      have hl : raw1491step0Labels = raw1491Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1491 raw1491Labels permutation32 permutation4
    mixedMoment B raw1491step0 raw1491step0Labels = mixedMoment B raw1491step1 raw1491step1Labels := by
      have ha : raw1491step1 = raw1491step0 := by apply Matrix.ext; unfold raw1491step1 raw1491step0; decide +kernel
      have hl : raw1491step0Labels = labelEmbedding7 ∘ raw1491step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1491step0 raw1491step0Labels raw1491step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4637 node4637Labels := by rfl

def raw1492 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1492Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw1492step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1492 raw1492Labels = mixedMoment B node1766 node1766Labels := by
  calc
    mixedMoment B raw1492 raw1492Labels = mixedMoment B raw1492step0 raw1492step0Labels := by
      have ha : raw1492step0 = (fun i j => raw1492 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1492step0 raw1492; decide +kernel
      have hl : raw1492step0Labels = raw1492Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1492 raw1492Labels permutation32 permutation4
    _ = mixedMoment B node1766 node1766Labels := by rfl

def raw1493 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1493Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw1493step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw1493step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1493step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw1493step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1493 raw1493Labels = mixedMoment B node1850 node1850Labels := by
  calc
    mixedMoment B raw1493 raw1493Labels = mixedMoment B raw1493step0 raw1493step0Labels := by
      have ha : raw1493step0 = (fun i j => raw1493 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1493step0 raw1493; decide +kernel
      have hl : raw1493step0Labels = raw1493Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1493 raw1493Labels permutation32 permutation6
    mixedMoment B raw1493step0 raw1493step0Labels = mixedMoment B raw1493step1 raw1493step1Labels := by
      have ha : raw1493step1 = -raw1493step0 := by apply Matrix.ext; change ∀ i j, raw1493step1 i j = -(raw1493step0 i j); unfold raw1493step1 raw1493step0; decide +kernel
      have hl : raw1493step1Labels = raw1493step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1493step1 raw1493step1Labels = mixedMoment B raw1493step2 raw1493step2Labels := by
      have ha : raw1493step2 = raw1493step1 := by apply Matrix.ext; unfold raw1493step2 raw1493step1; decide +kernel
      have hl : raw1493step1Labels = labelEmbedding1 ∘ raw1493step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1493step1 raw1493step1Labels raw1493step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1850 node1850Labels := by rfl

def raw1494 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1494Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1494step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1494step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1494 raw1494Labels = mixedMoment B node4638 node4638Labels := by
  calc
    mixedMoment B raw1494 raw1494Labels = mixedMoment B raw1494step0 raw1494step0Labels := by
      have ha : raw1494step0 = (fun i j => raw1494 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1494step0 raw1494; decide +kernel
      have hl : raw1494step0Labels = raw1494Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1494 raw1494Labels permutation32 permutation4
    mixedMoment B raw1494step0 raw1494step0Labels = mixedMoment B raw1494step1 raw1494step1Labels := by
      have ha : raw1494step1 = raw1494step0 := by apply Matrix.ext; unfold raw1494step1 raw1494step0; decide +kernel
      have hl : raw1494step0Labels = labelEmbedding7 ∘ raw1494step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1494step0 raw1494step0Labels raw1494step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4638 node4638Labels := by rfl

def raw1495 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1495Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw1495step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1495 raw1495Labels = mixedMoment B node1767 node1767Labels := by
  calc
    mixedMoment B raw1495 raw1495Labels = mixedMoment B raw1495step0 raw1495step0Labels := by
      have ha : raw1495step0 = (fun i j => raw1495 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1495step0 raw1495; decide +kernel
      have hl : raw1495step0Labels = raw1495Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1495 raw1495Labels permutation32 permutation4
    _ = mixedMoment B node1767 node1767Labels := by rfl

def raw1496 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 0, -1], ![0, 2, -2], ![-2, 3, -1]]
def raw1496Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw1496step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw1496step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw1496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1496 raw1496Labels = mixedMoment B node1851 node1851Labels := by
  calc
    mixedMoment B raw1496 raw1496Labels = mixedMoment B raw1496step0 raw1496step0Labels := by
      have ha : raw1496step0 = (fun i j => raw1496 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1496step0 raw1496; decide +kernel
      have hl : raw1496step0Labels = raw1496Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1496 raw1496Labels permutation33 permutation6
    mixedMoment B raw1496step0 raw1496step0Labels = mixedMoment B raw1496step1 raw1496step1Labels := by
      have ha : raw1496step1 = -raw1496step0 := by apply Matrix.ext; change ∀ i j, raw1496step1 i j = -(raw1496step0 i j); unfold raw1496step1 raw1496step0; decide +kernel
      have hl : raw1496step1Labels = raw1496step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1496step1 raw1496step1Labels = mixedMoment B raw1496step2 raw1496step2Labels := by
      have ha : raw1496step2 = raw1496step1 := by apply Matrix.ext; unfold raw1496step2 raw1496step1; decide +kernel
      have hl : raw1496step1Labels = labelEmbedding1 ∘ raw1496step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1496step1 raw1496step1Labels raw1496step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1851 node1851Labels := by rfl

def raw1497 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw1497Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1497step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1497step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1497step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1497 raw1497Labels = mixedMoment B node4639 node4639Labels := by
  calc
    mixedMoment B raw1497 raw1497Labels = mixedMoment B raw1497step0 raw1497step0Labels := by
      have ha : raw1497step0 = (fun i j => raw1497 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1497step0 raw1497; decide +kernel
      have hl : raw1497step0Labels = raw1497Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1497 raw1497Labels permutation152 permutation4
    mixedMoment B raw1497step0 raw1497step0Labels = mixedMoment B raw1497step1 raw1497step1Labels := by
      have ha : raw1497step1 = raw1497step0 := by apply Matrix.ext; unfold raw1497step1 raw1497step0; decide +kernel
      have hl : raw1497step0Labels = labelEmbedding7 ∘ raw1497step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1497step0 raw1497step0Labels raw1497step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4639 node4639Labels := by rfl

def raw1498 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw1498Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw1498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1498 raw1498Labels = mixedMoment B node1768 node1768Labels := by
  calc
    mixedMoment B raw1498 raw1498Labels = mixedMoment B raw1498step0 raw1498step0Labels := by
      have ha : raw1498step0 = (fun i j => raw1498 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1498step0 raw1498; decide +kernel
      have hl : raw1498step0Labels = raw1498Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1498 raw1498Labels permutation152 permutation4
    _ = mixedMoment B node1768 node1768Labels := by rfl

def raw1499 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 2, -3]]
def raw1499Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw1499step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1499step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1499step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1499step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1499step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1499 raw1499Labels = mixedMoment B node1834 node1834Labels := by
  calc
    mixedMoment B raw1499 raw1499Labels = mixedMoment B raw1499step0 raw1499step0Labels := by
      have ha : raw1499step0 = (fun i j => raw1499 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1499step0 raw1499; decide +kernel
      have hl : raw1499step0Labels = raw1499Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1499 raw1499Labels permutation152 permutation6
    mixedMoment B raw1499step0 raw1499step0Labels = mixedMoment B raw1499step1 raw1499step1Labels := by
      have ha : raw1499step1 = -raw1499step0 := by apply Matrix.ext; change ∀ i j, raw1499step1 i j = -(raw1499step0 i j); unfold raw1499step1 raw1499step0; decide +kernel
      have hl : raw1499step1Labels = raw1499step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1499step1 raw1499step1Labels = mixedMoment B raw1499step2 raw1499step2Labels := by
      have ha : raw1499step2 = raw1499step1 := by apply Matrix.ext; unfold raw1499step2 raw1499step1; decide +kernel
      have hl : raw1499step1Labels = labelEmbedding1 ∘ raw1499step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1499step1 raw1499step1Labels raw1499step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1834 node1834Labels := by rfl

def raw1500 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw1500Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1500step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1500step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1500 raw1500Labels = mixedMoment B node4640 node4640Labels := by
  calc
    mixedMoment B raw1500 raw1500Labels = mixedMoment B raw1500step0 raw1500step0Labels := by
      have ha : raw1500step0 = (fun i j => raw1500 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1500step0 raw1500; decide +kernel
      have hl : raw1500step0Labels = raw1500Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1500 raw1500Labels permutation152 permutation4
    mixedMoment B raw1500step0 raw1500step0Labels = mixedMoment B raw1500step1 raw1500step1Labels := by
      have ha : raw1500step1 = raw1500step0 := by apply Matrix.ext; unfold raw1500step1 raw1500step0; decide +kernel
      have hl : raw1500step0Labels = labelEmbedding7 ∘ raw1500step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1500step0 raw1500step0Labels raw1500step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4640 node4640Labels := by rfl

def raw1501 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw1501Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw1501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1501 raw1501Labels = mixedMoment B node1769 node1769Labels := by
  calc
    mixedMoment B raw1501 raw1501Labels = mixedMoment B raw1501step0 raw1501step0Labels := by
      have ha : raw1501step0 = (fun i j => raw1501 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1501step0 raw1501; decide +kernel
      have hl : raw1501step0Labels = raw1501Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1501 raw1501Labels permutation152 permutation4
    _ = mixedMoment B node1769 node1769Labels := by rfl

def raw1502 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![0, 2, -2]]
def raw1502Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw1502step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1502step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1502step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1502 raw1502Labels = mixedMoment B node1835 node1835Labels := by
  calc
    mixedMoment B raw1502 raw1502Labels = mixedMoment B raw1502step0 raw1502step0Labels := by
      have ha : raw1502step0 = (fun i j => raw1502 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1502step0 raw1502; decide +kernel
      have hl : raw1502step0Labels = raw1502Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1502 raw1502Labels permutation152 permutation6
    mixedMoment B raw1502step0 raw1502step0Labels = mixedMoment B raw1502step1 raw1502step1Labels := by
      have ha : raw1502step1 = -raw1502step0 := by apply Matrix.ext; change ∀ i j, raw1502step1 i j = -(raw1502step0 i j); unfold raw1502step1 raw1502step0; decide +kernel
      have hl : raw1502step1Labels = raw1502step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1502step1 raw1502step1Labels = mixedMoment B raw1502step2 raw1502step2Labels := by
      have ha : raw1502step2 = raw1502step1 := by apply Matrix.ext; unfold raw1502step2 raw1502step1; decide +kernel
      have hl : raw1502step1Labels = labelEmbedding1 ∘ raw1502step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1502step1 raw1502step1Labels raw1502step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1835 node1835Labels := by rfl

def raw1503 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1503Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1503step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1503step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1503step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1503 raw1503Labels = mixedMoment B node4642 node4642Labels := by
  calc
    mixedMoment B raw1503 raw1503Labels = mixedMoment B raw1503step0 raw1503step0Labels := by
      have ha : raw1503step0 = (fun i j => raw1503 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1503step0 raw1503; decide +kernel
      have hl : raw1503step0Labels = raw1503Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1503 raw1503Labels permutation152 permutation4
    mixedMoment B raw1503step0 raw1503step0Labels = mixedMoment B raw1503step1 raw1503step1Labels := by
      have ha : raw1503step1 = raw1503step0 := by apply Matrix.ext; unfold raw1503step1 raw1503step0; decide +kernel
      have hl : raw1503step0Labels = labelEmbedding7 ∘ raw1503step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1503step0 raw1503step0Labels raw1503step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4642 node4642Labels := by rfl

def raw1504 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1504Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1504 raw1504Labels = mixedMoment B node1771 node1771Labels := by
  calc
    mixedMoment B raw1504 raw1504Labels = mixedMoment B raw1504step0 raw1504step0Labels := by
      have ha : raw1504step0 = (fun i j => raw1504 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1504step0 raw1504; decide +kernel
      have hl : raw1504step0Labels = raw1504Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1504 raw1504Labels permutation152 permutation4
    _ = mixedMoment B node1771 node1771Labels := by rfl

def raw1505 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![-1, 2, -1]]
def raw1505Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw1505step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1505step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1505step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1505step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1505step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1505 raw1505Labels = mixedMoment B node1838 node1838Labels := by
  calc
    mixedMoment B raw1505 raw1505Labels = mixedMoment B raw1505step0 raw1505step0Labels := by
      have ha : raw1505step0 = (fun i j => raw1505 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1505step0 raw1505; decide +kernel
      have hl : raw1505step0Labels = raw1505Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1505 raw1505Labels permutation153 permutation6
    mixedMoment B raw1505step0 raw1505step0Labels = mixedMoment B raw1505step1 raw1505step1Labels := by
      have ha : raw1505step1 = -raw1505step0 := by apply Matrix.ext; change ∀ i j, raw1505step1 i j = -(raw1505step0 i j); unfold raw1505step1 raw1505step0; decide +kernel
      have hl : raw1505step1Labels = raw1505step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1505step1 raw1505step1Labels = mixedMoment B raw1505step2 raw1505step2Labels := by
      have ha : raw1505step2 = raw1505step1 := by apply Matrix.ext; unfold raw1505step2 raw1505step1; decide +kernel
      have hl : raw1505step1Labels = labelEmbedding1 ∘ raw1505step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1505step1 raw1505step1Labels raw1505step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1838 node1838Labels := by rfl

def raw1506 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1506Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1506step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1506step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1506 raw1506Labels = mixedMoment B node4644 node4644Labels := by
  calc
    mixedMoment B raw1506 raw1506Labels = mixedMoment B raw1506step0 raw1506step0Labels := by
      have ha : raw1506step0 = (fun i j => raw1506 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1506step0 raw1506; decide +kernel
      have hl : raw1506step0Labels = raw1506Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1506 raw1506Labels permutation32 permutation4
    mixedMoment B raw1506step0 raw1506step0Labels = mixedMoment B raw1506step1 raw1506step1Labels := by
      have ha : raw1506step1 = raw1506step0 := by apply Matrix.ext; unfold raw1506step1 raw1506step0; decide +kernel
      have hl : raw1506step0Labels = labelEmbedding7 ∘ raw1506step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1506step0 raw1506step0Labels raw1506step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4644 node4644Labels := by rfl

def raw1507 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1507Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw1507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1507 raw1507Labels = mixedMoment B node1773 node1773Labels := by
  calc
    mixedMoment B raw1507 raw1507Labels = mixedMoment B raw1507step0 raw1507step0Labels := by
      have ha : raw1507step0 = (fun i j => raw1507 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1507step0 raw1507; decide +kernel
      have hl : raw1507step0Labels = raw1507Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1507 raw1507Labels permutation32 permutation4
    _ = mixedMoment B node1773 node1773Labels := by rfl

def raw1508 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![-1, 3, -2]]
def raw1508Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, -1, 3]]
def raw1508step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw1508step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1508step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw1508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1508 raw1508Labels = mixedMoment B node1841 node1841Labels := by
  calc
    mixedMoment B raw1508 raw1508Labels = mixedMoment B raw1508step0 raw1508step0Labels := by
      have ha : raw1508step0 = (fun i j => raw1508 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1508step0 raw1508; decide +kernel
      have hl : raw1508step0Labels = raw1508Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1508 raw1508Labels permutation32 permutation6
    mixedMoment B raw1508step0 raw1508step0Labels = mixedMoment B raw1508step1 raw1508step1Labels := by
      have ha : raw1508step1 = -raw1508step0 := by apply Matrix.ext; change ∀ i j, raw1508step1 i j = -(raw1508step0 i j); unfold raw1508step1 raw1508step0; decide +kernel
      have hl : raw1508step1Labels = raw1508step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1508step1 raw1508step1Labels = mixedMoment B raw1508step2 raw1508step2Labels := by
      have ha : raw1508step2 = raw1508step1 := by apply Matrix.ext; unfold raw1508step2 raw1508step1; decide +kernel
      have hl : raw1508step1Labels = labelEmbedding1 ∘ raw1508step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1508step1 raw1508step1Labels raw1508step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1841 node1841Labels := by rfl

def raw1509 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw1509Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1509step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1509step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1509 raw1509Labels = mixedMoment B node4645 node4645Labels := by
  calc
    mixedMoment B raw1509 raw1509Labels = mixedMoment B raw1509step0 raw1509step0Labels := by
      have ha : raw1509step0 = (fun i j => raw1509 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1509step0 raw1509; decide +kernel
      have hl : raw1509step0Labels = raw1509Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1509 raw1509Labels permutation32 permutation4
    mixedMoment B raw1509step0 raw1509step0Labels = mixedMoment B raw1509step1 raw1509step1Labels := by
      have ha : raw1509step1 = raw1509step0 := by apply Matrix.ext; unfold raw1509step1 raw1509step0; decide +kernel
      have hl : raw1509step0Labels = labelEmbedding7 ∘ raw1509step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1509step0 raw1509step0Labels raw1509step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4645 node4645Labels := by rfl

def raw1510 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw1510Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw1510step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1510 raw1510Labels = mixedMoment B node1774 node1774Labels := by
  calc
    mixedMoment B raw1510 raw1510Labels = mixedMoment B raw1510step0 raw1510step0Labels := by
      have ha : raw1510step0 = (fun i j => raw1510 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1510step0 raw1510; decide +kernel
      have hl : raw1510step0Labels = raw1510Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1510 raw1510Labels permutation32 permutation4
    _ = mixedMoment B node1774 node1774Labels := by rfl

def raw1511 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![-1, 1, 0], ![-1, 2, -1], ![1, 2, -3]]
def raw1511Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-3, 1, 2]]
def raw1511step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw1511step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1511step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw1511step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1511 raw1511Labels = mixedMoment B node1840 node1840Labels := by
  calc
    mixedMoment B raw1511 raw1511Labels = mixedMoment B raw1511step0 raw1511step0Labels := by
      have ha : raw1511step0 = (fun i j => raw1511 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1511step0 raw1511; decide +kernel
      have hl : raw1511step0Labels = raw1511Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1511 raw1511Labels permutation32 permutation6
    mixedMoment B raw1511step0 raw1511step0Labels = mixedMoment B raw1511step1 raw1511step1Labels := by
      have ha : raw1511step1 = -raw1511step0 := by apply Matrix.ext; change ∀ i j, raw1511step1 i j = -(raw1511step0 i j); unfold raw1511step1 raw1511step0; decide +kernel
      have hl : raw1511step1Labels = raw1511step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1511step1 raw1511step1Labels = mixedMoment B raw1511step2 raw1511step2Labels := by
      have ha : raw1511step2 = raw1511step1 := by apply Matrix.ext; unfold raw1511step2 raw1511step1; decide +kernel
      have hl : raw1511step1Labels = labelEmbedding1 ∘ raw1511step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1511step1 raw1511step1Labels raw1511step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1840 node1840Labels := by rfl

def raw1512 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1512Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1512step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1512step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1512 raw1512Labels = mixedMoment B node4648 node4648Labels := by
  calc
    mixedMoment B raw1512 raw1512Labels = mixedMoment B raw1512step0 raw1512step0Labels := by
      have ha : raw1512step0 = (fun i j => raw1512 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1512step0 raw1512; decide +kernel
      have hl : raw1512step0Labels = raw1512Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1512 raw1512Labels permutation152 permutation4
    mixedMoment B raw1512step0 raw1512step0Labels = mixedMoment B raw1512step1 raw1512step1Labels := by
      have ha : raw1512step1 = raw1512step0 := by apply Matrix.ext; unfold raw1512step1 raw1512step0; decide +kernel
      have hl : raw1512step0Labels = labelEmbedding7 ∘ raw1512step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1512step0 raw1512step0Labels raw1512step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4648 node4648Labels := by rfl

def raw1513 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1513 raw1513Labels = mixedMoment B node1776 node1776Labels := by
  calc
    mixedMoment B raw1513 raw1513Labels = mixedMoment B raw1513step0 raw1513step0Labels := by
      have ha : raw1513step0 = (fun i j => raw1513 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1513step0 raw1513; decide +kernel
      have hl : raw1513step0Labels = raw1513Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1513 raw1513Labels permutation152 permutation4
    _ = mixedMoment B node1776 node1776Labels := by rfl

def raw1514 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1514Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw1514step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1514step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1514step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1514step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1514 raw1514Labels = mixedMoment B node1844 node1844Labels := by
  calc
    mixedMoment B raw1514 raw1514Labels = mixedMoment B raw1514step0 raw1514step0Labels := by
      have ha : raw1514step0 = (fun i j => raw1514 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1514step0 raw1514; decide +kernel
      have hl : raw1514step0Labels = raw1514Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1514 raw1514Labels permutation170 permutation6
    mixedMoment B raw1514step0 raw1514step0Labels = mixedMoment B raw1514step1 raw1514step1Labels := by
      have ha : raw1514step1 = -raw1514step0 := by apply Matrix.ext; change ∀ i j, raw1514step1 i j = -(raw1514step0 i j); unfold raw1514step1 raw1514step0; decide +kernel
      have hl : raw1514step1Labels = raw1514step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1514step1 raw1514step1Labels = mixedMoment B raw1514step2 raw1514step2Labels := by
      have ha : raw1514step2 = raw1514step1 := by apply Matrix.ext; unfold raw1514step2 raw1514step1; decide +kernel
      have hl : raw1514step1Labels = labelEmbedding1 ∘ raw1514step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1514step1 raw1514step1Labels raw1514step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1844 node1844Labels := by rfl

def raw1515 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1515Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1515step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1515step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1515 raw1515Labels = mixedMoment B node4650 node4650Labels := by
  calc
    mixedMoment B raw1515 raw1515Labels = mixedMoment B raw1515step0 raw1515step0Labels := by
      have ha : raw1515step0 = (fun i j => raw1515 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1515step0 raw1515; decide +kernel
      have hl : raw1515step0Labels = raw1515Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1515 raw1515Labels permutation32 permutation4
    mixedMoment B raw1515step0 raw1515step0Labels = mixedMoment B raw1515step1 raw1515step1Labels := by
      have ha : raw1515step1 = raw1515step0 := by apply Matrix.ext; unfold raw1515step1 raw1515step0; decide +kernel
      have hl : raw1515step0Labels = labelEmbedding7 ∘ raw1515step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1515step0 raw1515step0Labels raw1515step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4650 node4650Labels := by rfl

def raw1516 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1516Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw1516step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1516 raw1516Labels = mixedMoment B node1778 node1778Labels := by
  calc
    mixedMoment B raw1516 raw1516Labels = mixedMoment B raw1516step0 raw1516step0Labels := by
      have ha : raw1516step0 = (fun i j => raw1516 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1516step0 raw1516; decide +kernel
      have hl : raw1516step0Labels = raw1516Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1516 raw1516Labels permutation32 permutation4
    _ = mixedMoment B node1778 node1778Labels := by rfl

def raw1517 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![0, 1, -1], ![1, 1, -2], ![-2, 3, -1]]
def raw1517Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw1517step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw1517step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw1517step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1517 raw1517Labels = mixedMoment B node1854 node1854Labels := by
  calc
    mixedMoment B raw1517 raw1517Labels = mixedMoment B raw1517step0 raw1517step0Labels := by
      have ha : raw1517step0 = (fun i j => raw1517 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1517step0 raw1517; decide +kernel
      have hl : raw1517step0Labels = raw1517Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1517 raw1517Labels permutation33 permutation6
    mixedMoment B raw1517step0 raw1517step0Labels = mixedMoment B raw1517step1 raw1517step1Labels := by
      have ha : raw1517step1 = -raw1517step0 := by apply Matrix.ext; change ∀ i j, raw1517step1 i j = -(raw1517step0 i j); unfold raw1517step1 raw1517step0; decide +kernel
      have hl : raw1517step1Labels = raw1517step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1517step1 raw1517step1Labels = mixedMoment B raw1517step2 raw1517step2Labels := by
      have ha : raw1517step2 = raw1517step1 := by apply Matrix.ext; unfold raw1517step2 raw1517step1; decide +kernel
      have hl : raw1517step1Labels = labelEmbedding1 ∘ raw1517step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1517step1 raw1517step1Labels raw1517step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1854 node1854Labels := by rfl

def raw1518 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw1518step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1518step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw1518step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1518 raw1518Labels = mixedMoment B node4651 node4651Labels := by
  calc
    mixedMoment B raw1518 raw1518Labels = mixedMoment B raw1518step0 raw1518step0Labels := by
      have ha : raw1518step0 = (fun i j => raw1518 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1518step0 raw1518; decide +kernel
      have hl : raw1518step0Labels = raw1518Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1518 raw1518Labels permutation32 permutation4
    mixedMoment B raw1518step0 raw1518step0Labels = mixedMoment B raw1518step1 raw1518step1Labels := by
      have ha : raw1518step1 = raw1518step0 := by apply Matrix.ext; unfold raw1518step1 raw1518step0; decide +kernel
      have hl : raw1518step0Labels = labelEmbedding7 ∘ raw1518step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1518step0 raw1518step0Labels raw1518step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4651 node4651Labels := by rfl

def raw1519 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1519Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw1519step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1519 raw1519Labels = mixedMoment B node1779 node1779Labels := by
  calc
    mixedMoment B raw1519 raw1519Labels = mixedMoment B raw1519step0 raw1519step0Labels := by
      have ha : raw1519step0 = (fun i j => raw1519 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1519step0 raw1519; decide +kernel
      have hl : raw1519step0Labels = raw1519Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1519 raw1519Labels permutation32 permutation4
    _ = mixedMoment B node1779 node1779Labels := by rfl

def raw1520 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![1, 2, -3]]
def raw1520Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-3, 1, 2]]
def raw1520step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def raw1520step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1520step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def raw1520step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1520 raw1520Labels = mixedMoment B node1845 node1845Labels := by
  calc
    mixedMoment B raw1520 raw1520Labels = mixedMoment B raw1520step0 raw1520step0Labels := by
      have ha : raw1520step0 = (fun i j => raw1520 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1520step0 raw1520; decide +kernel
      have hl : raw1520step0Labels = raw1520Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1520 raw1520Labels permutation34 permutation6
    mixedMoment B raw1520step0 raw1520step0Labels = mixedMoment B raw1520step1 raw1520step1Labels := by
      have ha : raw1520step1 = -raw1520step0 := by apply Matrix.ext; change ∀ i j, raw1520step1 i j = -(raw1520step0 i j); unfold raw1520step1 raw1520step0; decide +kernel
      have hl : raw1520step1Labels = raw1520step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1520step1 raw1520step1Labels = mixedMoment B raw1520step2 raw1520step2Labels := by
      have ha : raw1520step2 = raw1520step1 := by apply Matrix.ext; unfold raw1520step2 raw1520step1; decide +kernel
      have hl : raw1520step1Labels = labelEmbedding1 ∘ raw1520step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1520step1 raw1520step1Labels raw1520step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1845 node1845Labels := by rfl

def raw1521 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1521step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1521step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1521 raw1521Labels = mixedMoment B node4653 node4653Labels := by
  calc
    mixedMoment B raw1521 raw1521Labels = mixedMoment B raw1521step0 raw1521step0Labels := by
      have ha : raw1521step0 = (fun i j => raw1521 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1521step0 raw1521; decide +kernel
      have hl : raw1521step0Labels = raw1521Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1521 raw1521Labels permutation32 permutation4
    mixedMoment B raw1521step0 raw1521step0Labels = mixedMoment B raw1521step1 raw1521step1Labels := by
      have ha : raw1521step1 = raw1521step0 := by apply Matrix.ext; unfold raw1521step1 raw1521step0; decide +kernel
      have hl : raw1521step0Labels = labelEmbedding7 ∘ raw1521step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1521step0 raw1521step0Labels raw1521step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4653 node4653Labels := by rfl

def raw1522 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw1522step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1522 raw1522Labels = mixedMoment B node1781 node1781Labels := by
  calc
    mixedMoment B raw1522 raw1522Labels = mixedMoment B raw1522step0 raw1522step0Labels := by
      have ha : raw1522step0 = (fun i j => raw1522 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1522step0 raw1522; decide +kernel
      have hl : raw1522step0Labels = raw1522Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1522 raw1522Labels permutation32 permutation4
    _ = mixedMoment B node1781 node1781Labels := by rfl

def raw1523 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 1, -2], ![-2, 2, 0], ![0, 2, -2]]
def raw1523Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw1523step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw1523step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1523step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw1523step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1523 raw1523Labels = mixedMoment B node1846 node1846Labels := by
  calc
    mixedMoment B raw1523 raw1523Labels = mixedMoment B raw1523step0 raw1523step0Labels := by
      have ha : raw1523step0 = (fun i j => raw1523 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1523step0 raw1523; decide +kernel
      have hl : raw1523step0Labels = raw1523Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1523 raw1523Labels permutation34 permutation6
    mixedMoment B raw1523step0 raw1523step0Labels = mixedMoment B raw1523step1 raw1523step1Labels := by
      have ha : raw1523step1 = -raw1523step0 := by apply Matrix.ext; change ∀ i j, raw1523step1 i j = -(raw1523step0 i j); unfold raw1523step1 raw1523step0; decide +kernel
      have hl : raw1523step1Labels = raw1523step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1523step1 raw1523step1Labels = mixedMoment B raw1523step2 raw1523step2Labels := by
      have ha : raw1523step2 = raw1523step1 := by apply Matrix.ext; unfold raw1523step2 raw1523step1; decide +kernel
      have hl : raw1523step1Labels = labelEmbedding1 ∘ raw1523step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1523step1 raw1523step1Labels raw1523step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1846 node1846Labels := by rfl

def raw1524 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1524step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1524step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1524 raw1524Labels = mixedMoment B node4654 node4654Labels := by
  calc
    mixedMoment B raw1524 raw1524Labels = mixedMoment B raw1524step0 raw1524step0Labels := by
      have ha : raw1524step0 = (fun i j => raw1524 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1524step0 raw1524; decide +kernel
      have hl : raw1524step0Labels = raw1524Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1524 raw1524Labels permutation32 permutation4
    mixedMoment B raw1524step0 raw1524step0Labels = mixedMoment B raw1524step1 raw1524step1Labels := by
      have ha : raw1524step1 = raw1524step0 := by apply Matrix.ext; unfold raw1524step1 raw1524step0; decide +kernel
      have hl : raw1524step0Labels = labelEmbedding7 ∘ raw1524step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1524step0 raw1524step0Labels raw1524step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4654 node4654Labels := by rfl

def raw1525 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw1525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1525 raw1525Labels = mixedMoment B node1782 node1782Labels := by
  calc
    mixedMoment B raw1525 raw1525Labels = mixedMoment B raw1525step0 raw1525step0Labels := by
      have ha : raw1525step0 = (fun i j => raw1525 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1525step0 raw1525; decide +kernel
      have hl : raw1525step0Labels = raw1525Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1525 raw1525Labels permutation32 permutation4
    _ = mixedMoment B node1782 node1782Labels := by rfl

def raw1526 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 1, -2], ![-1, 2, -1], ![-1, 2, -1]]
def raw1526Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw1526step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1526step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw1526step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1526step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw1526step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1526 raw1526Labels = mixedMoment B node1855 node1855Labels := by
  calc
    mixedMoment B raw1526 raw1526Labels = mixedMoment B raw1526step0 raw1526step0Labels := by
      have ha : raw1526step0 = (fun i j => raw1526 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1526step0 raw1526; decide +kernel
      have hl : raw1526step0Labels = raw1526Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1526 raw1526Labels permutation35 permutation6
    mixedMoment B raw1526step0 raw1526step0Labels = mixedMoment B raw1526step1 raw1526step1Labels := by
      have ha : raw1526step1 = -raw1526step0 := by apply Matrix.ext; change ∀ i j, raw1526step1 i j = -(raw1526step0 i j); unfold raw1526step1 raw1526step0; decide +kernel
      have hl : raw1526step1Labels = raw1526step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1526step1 raw1526step1Labels = mixedMoment B raw1526step2 raw1526step2Labels := by
      have ha : raw1526step2 = raw1526step1 := by apply Matrix.ext; unfold raw1526step2 raw1526step1; decide +kernel
      have hl : raw1526step1Labels = labelEmbedding1 ∘ raw1526step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1526step1 raw1526step1Labels raw1526step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1855 node1855Labels := by rfl

def raw1527 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 2, -3], ![-2, 3, -1]]
def raw1527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1527step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw1527step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw1527step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1527 raw1527Labels = mixedMoment B node4657 node4657Labels := by
  calc
    mixedMoment B raw1527 raw1527Labels = mixedMoment B raw1527step0 raw1527step0Labels := by
      have ha : raw1527step0 = (fun i j => raw1527 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1527step0 raw1527; decide +kernel
      have hl : raw1527step0Labels = raw1527Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1527 raw1527Labels permutation8 permutation4
    mixedMoment B raw1527step0 raw1527step0Labels = mixedMoment B raw1527step1 raw1527step1Labels := by
      have ha : raw1527step1 = raw1527step0 := by apply Matrix.ext; unfold raw1527step1 raw1527step0; decide +kernel
      have hl : raw1527step0Labels = labelEmbedding7 ∘ raw1527step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1527step0 raw1527step0Labels raw1527step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4657 node4657Labels := by rfl

def raw1528 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 2, -3], ![-2, 3, -1]]
def raw1528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1528step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw1528step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1528 raw1528Labels = mixedMoment B node1783 node1783Labels := by
  calc
    mixedMoment B raw1528 raw1528Labels = mixedMoment B raw1528step0 raw1528step0Labels := by
      have ha : raw1528step0 = (fun i j => raw1528 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1528step0 raw1528; decide +kernel
      have hl : raw1528step0Labels = raw1528Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1528 raw1528Labels permutation8 permutation4
    _ = mixedMoment B node1783 node1783Labels := by rfl

def raw1529 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, -3, 3], ![1, -2, 1], ![1, 2, -3], ![-2, 3, -1]]
def raw1529Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1529step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 1, -2], ![-1, -2, 3], ![-3, 1, 2]]
def raw1529step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1529step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 2, -3], ![3, -1, -2]]
def raw1529step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1529step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, 2, -3], ![3, -1, -2]]
def raw1529step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1529 raw1529Labels = mixedMoment B node1857 node1857Labels := by
  calc
    mixedMoment B raw1529 raw1529Labels = mixedMoment B raw1529step0 raw1529step0Labels := by
      have ha : raw1529step0 = (fun i j => raw1529 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1529step0 raw1529; decide +kernel
      have hl : raw1529step0Labels = raw1529Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1529 raw1529Labels permutation9 permutation6
    mixedMoment B raw1529step0 raw1529step0Labels = mixedMoment B raw1529step1 raw1529step1Labels := by
      have ha : raw1529step1 = -raw1529step0 := by apply Matrix.ext; change ∀ i j, raw1529step1 i j = -(raw1529step0 i j); unfold raw1529step1 raw1529step0; decide +kernel
      have hl : raw1529step1Labels = raw1529step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1529step1 raw1529step1Labels = mixedMoment B raw1529step2 raw1529step2Labels := by
      have ha : raw1529step2 = raw1529step1 := by apply Matrix.ext; unfold raw1529step2 raw1529step1; decide +kernel
      have hl : raw1529step1Labels = labelEmbedding1 ∘ raw1529step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1529step1 raw1529step1Labels raw1529step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1857 node1857Labels := by rfl

def raw1530 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1530step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1530step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1530 raw1530Labels = mixedMoment B node4658 node4658Labels := by
  calc
    mixedMoment B raw1530 raw1530Labels = mixedMoment B raw1530step0 raw1530step0Labels := by
      have ha : raw1530step0 = (fun i j => raw1530 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1530step0 raw1530; decide +kernel
      have hl : raw1530step0Labels = raw1530Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1530 raw1530Labels permutation152 permutation4
    mixedMoment B raw1530step0 raw1530step0Labels = mixedMoment B raw1530step1 raw1530step1Labels := by
      have ha : raw1530step1 = raw1530step0 := by apply Matrix.ext; unfold raw1530step1 raw1530step0; decide +kernel
      have hl : raw1530step0Labels = labelEmbedding7 ∘ raw1530step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1530step0 raw1530step0Labels raw1530step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4658 node4658Labels := by rfl

def raw1531 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1531step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1531step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1531 raw1531Labels = mixedMoment B node1784 node1784Labels := by
  calc
    mixedMoment B raw1531 raw1531Labels = mixedMoment B raw1531step0 raw1531step0Labels := by
      have ha : raw1531step0 = (fun i j => raw1531 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1531step0 raw1531; decide +kernel
      have hl : raw1531step0Labels = raw1531Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1531 raw1531Labels permutation152 permutation4
    _ = mixedMoment B node1784 node1784Labels := by rfl

def raw1532 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1532Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw1532step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1532step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw1532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1532 raw1532Labels = mixedMoment B node1884 node1884Labels := by
  calc
    mixedMoment B raw1532 raw1532Labels = mixedMoment B raw1532step0 raw1532step0Labels := by
      have ha : raw1532step0 = (fun i j => raw1532 (permutation686 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1532step0 raw1532; decide +kernel
      have hl : raw1532step0Labels = raw1532Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1532 raw1532Labels permutation686 permutation6
    mixedMoment B raw1532step0 raw1532step0Labels = mixedMoment B raw1532step1 raw1532step1Labels := by
      have ha : raw1532step1 = raw1532step0 := by apply Matrix.ext; unfold raw1532step1 raw1532step0; decide +kernel
      have hl : raw1532step0Labels = labelEmbedding1 ∘ raw1532step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1532step0 raw1532step0Labels raw1532step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1884 node1884Labels := by rfl

def raw1533 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1533Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1533step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1533step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1533step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1533 raw1533Labels = mixedMoment B node4659 node4659Labels := by
  calc
    mixedMoment B raw1533 raw1533Labels = mixedMoment B raw1533step0 raw1533step0Labels := by
      have ha : raw1533step0 = (fun i j => raw1533 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1533step0 raw1533; decide +kernel
      have hl : raw1533step0Labels = raw1533Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1533 raw1533Labels permutation152 permutation4
    mixedMoment B raw1533step0 raw1533step0Labels = mixedMoment B raw1533step1 raw1533step1Labels := by
      have ha : raw1533step1 = raw1533step0 := by apply Matrix.ext; unfold raw1533step1 raw1533step0; decide +kernel
      have hl : raw1533step0Labels = labelEmbedding7 ∘ raw1533step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1533step0 raw1533step0Labels raw1533step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4659 node4659Labels := by rfl

def raw1534 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1534step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1534 raw1534Labels = mixedMoment B node1785 node1785Labels := by
  calc
    mixedMoment B raw1534 raw1534Labels = mixedMoment B raw1534step0 raw1534step0Labels := by
      have ha : raw1534step0 = (fun i j => raw1534 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1534step0 raw1534; decide +kernel
      have hl : raw1534step0Labels = raw1534Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1534 raw1534Labels permutation152 permutation4
    _ = mixedMoment B node1785 node1785Labels := by rfl

def raw1535 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -3, 3], ![2, -2, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1535Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw1535step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1535step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1535step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1535step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1535step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1535 raw1535Labels = mixedMoment B node1981 node1981Labels := by
  calc
    mixedMoment B raw1535 raw1535Labels = mixedMoment B raw1535step0 raw1535step0Labels := by
      have ha : raw1535step0 = (fun i j => raw1535 (permutation176 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1535step0 raw1535; decide +kernel
      have hl : raw1535step0Labels = raw1535Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1535 raw1535Labels permutation176 permutation6
    mixedMoment B raw1535step0 raw1535step0Labels = mixedMoment B raw1535step1 raw1535step1Labels := by
      have ha : raw1535step1 = -raw1535step0 := by apply Matrix.ext; change ∀ i j, raw1535step1 i j = -(raw1535step0 i j); unfold raw1535step1 raw1535step0; decide +kernel
      have hl : raw1535step1Labels = raw1535step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1535step1 raw1535step1Labels = mixedMoment B raw1535step2 raw1535step2Labels := by
      have ha : raw1535step2 = raw1535step1 := by apply Matrix.ext; unfold raw1535step2 raw1535step1; decide +kernel
      have hl : raw1535step1Labels = labelEmbedding1 ∘ raw1535step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1535step1 raw1535step1Labels raw1535step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1981 node1981Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
