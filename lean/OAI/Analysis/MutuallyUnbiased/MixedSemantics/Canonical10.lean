import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw1280 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![1, 0, -1], ![-2, 4, -2]]
def raw1280Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1280step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-2, -2, 4]]
def raw1280step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1280step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw1280step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1280step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![2, 2, -4]]
def raw1280step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1280 raw1280Labels = mixedMoment B node1752 node1752Labels := by
  calc
    mixedMoment B raw1280 raw1280Labels = mixedMoment B raw1280step0 raw1280step0Labels := by
      have ha : raw1280step0 = (fun i j => raw1280 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1280step0 raw1280; decide +kernel
      have hl : raw1280step0Labels = raw1280Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1280 raw1280Labels permutation2 permutation6
    mixedMoment B raw1280step0 raw1280step0Labels = mixedMoment B raw1280step1 raw1280step1Labels := by
      have ha : raw1280step1 = -raw1280step0 := by apply Matrix.ext; change ∀ i j, raw1280step1 i j = -(raw1280step0 i j); unfold raw1280step1 raw1280step0; decide +kernel
      have hl : raw1280step1Labels = raw1280step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1280step1 raw1280step1Labels = mixedMoment B raw1280step2 raw1280step2Labels := by
      have ha : raw1280step2 = raw1280step1 := by apply Matrix.ext; unfold raw1280step2 raw1280step1; decide +kernel
      have hl : raw1280step1Labels = labelEmbedding1 ∘ raw1280step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1280step1 raw1280step1Labels raw1280step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1752 node1752Labels := by rfl

def raw1281 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1281step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1281 raw1281Labels = mixedMoment B node4489 node4489Labels := by
  calc
    mixedMoment B raw1281 raw1281Labels = mixedMoment B raw1281step0 raw1281step0Labels := by
      have ha : raw1281step0 = (fun i j => raw1281 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1281step0 raw1281; decide +kernel
      have hl : raw1281step0Labels = raw1281Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1281 raw1281Labels permutation32 permutation4
    mixedMoment B raw1281step0 raw1281step0Labels = mixedMoment B raw1281step1 raw1281step1Labels := by
      have ha : raw1281step1 = raw1281step0 := by apply Matrix.ext; unfold raw1281step1 raw1281step0; decide +kernel
      have hl : raw1281step0Labels = labelEmbedding7 ∘ raw1281step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1281step0 raw1281step0Labels raw1281step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4489 node4489Labels := by rfl

def raw1282 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1282Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1282step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1282 raw1282Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw1282 raw1282Labels = mixedMoment B raw1282step0 raw1282step0Labels := by
      have ha : raw1282step0 = (fun i j => raw1282 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1282step0 raw1282; decide +kernel
      have hl : raw1282step0Labels = raw1282Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1282 raw1282Labels permutation32 permutation4
    _ = mixedMoment B node1073 node1073Labels := by rfl

def raw1283 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2]]
def raw1283Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw1283step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1283step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1283step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1283 raw1283Labels = mixedMoment B node1648 node1648Labels := by
  calc
    mixedMoment B raw1283 raw1283Labels = mixedMoment B raw1283step0 raw1283step0Labels := by
      have ha : raw1283step0 = (fun i j => raw1283 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1283step0 raw1283; decide +kernel
      have hl : raw1283step0Labels = raw1283Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1283 raw1283Labels permutation32 permutation6
    mixedMoment B raw1283step0 raw1283step0Labels = mixedMoment B raw1283step1 raw1283step1Labels := by
      have ha : raw1283step1 = -raw1283step0 := by apply Matrix.ext; change ∀ i j, raw1283step1 i j = -(raw1283step0 i j); unfold raw1283step1 raw1283step0; decide +kernel
      have hl : raw1283step1Labels = raw1283step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1283step1 raw1283step1Labels = mixedMoment B raw1283step2 raw1283step2Labels := by
      have ha : raw1283step2 = raw1283step1 := by apply Matrix.ext; unfold raw1283step2 raw1283step1; decide +kernel
      have hl : raw1283step1Labels = labelEmbedding1 ∘ raw1283step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1283step1 raw1283step1Labels raw1283step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1648 node1648Labels := by rfl

def raw1284 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 2, -3]]
def raw1284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1284step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw1284step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1284step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw1284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1284 raw1284Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw1284 raw1284Labels = mixedMoment B raw1284step0 raw1284step0Labels := by
      have ha : raw1284step0 = (fun i j => raw1284 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1284step0 raw1284; decide +kernel
      have hl : raw1284step0Labels = raw1284Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1284 raw1284Labels permutation8 permutation4
    mixedMoment B raw1284step0 raw1284step0Labels = mixedMoment B raw1284step1 raw1284step1Labels := by
      have ha : raw1284step1 = raw1284step0 := by apply Matrix.ext; unfold raw1284step1 raw1284step0; decide +kernel
      have hl : raw1284step0Labels = labelEmbedding7 ∘ raw1284step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1284step0 raw1284step0Labels raw1284step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4490 node4490Labels := by rfl

def raw1285 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 2, -3]]
def raw1285Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1285step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw1285step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1285 raw1285Labels = mixedMoment B node1074 node1074Labels := by
  calc
    mixedMoment B raw1285 raw1285Labels = mixedMoment B raw1285step0 raw1285step0Labels := by
      have ha : raw1285step0 = (fun i j => raw1285 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1285step0 raw1285; decide +kernel
      have hl : raw1285step0Labels = raw1285Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1285 raw1285Labels permutation8 permutation4
    _ = mixedMoment B node1074 node1074Labels := by rfl

def raw1286 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 2, -3]]
def raw1286Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1286step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw1286step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1286step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1286step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1286step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1286step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1286 raw1286Labels = mixedMoment B node1650 node1650Labels := by
  calc
    mixedMoment B raw1286 raw1286Labels = mixedMoment B raw1286step0 raw1286step0Labels := by
      have ha : raw1286step0 = (fun i j => raw1286 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1286step0 raw1286; decide +kernel
      have hl : raw1286step0Labels = raw1286Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1286 raw1286Labels permutation8 permutation6
    mixedMoment B raw1286step0 raw1286step0Labels = mixedMoment B raw1286step1 raw1286step1Labels := by
      have ha : raw1286step1 = -raw1286step0 := by apply Matrix.ext; change ∀ i j, raw1286step1 i j = -(raw1286step0 i j); unfold raw1286step1 raw1286step0; decide +kernel
      have hl : raw1286step1Labels = raw1286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1286step1 raw1286step1Labels = mixedMoment B raw1286step2 raw1286step2Labels := by
      have ha : raw1286step2 = raw1286step1 := by apply Matrix.ext; unfold raw1286step2 raw1286step1; decide +kernel
      have hl : raw1286step1Labels = labelEmbedding1 ∘ raw1286step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1286step1 raw1286step1Labels raw1286step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1650 node1650Labels := by rfl

def raw1287 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw1287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1287step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw1287step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1287step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw1287step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1287 raw1287Labels = mixedMoment B node4491 node4491Labels := by
  calc
    mixedMoment B raw1287 raw1287Labels = mixedMoment B raw1287step0 raw1287step0Labels := by
      have ha : raw1287step0 = (fun i j => raw1287 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1287step0 raw1287; decide +kernel
      have hl : raw1287step0Labels = raw1287Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1287 raw1287Labels permutation8 permutation4
    mixedMoment B raw1287step0 raw1287step0Labels = mixedMoment B raw1287step1 raw1287step1Labels := by
      have ha : raw1287step1 = raw1287step0 := by apply Matrix.ext; unfold raw1287step1 raw1287step0; decide +kernel
      have hl : raw1287step0Labels = labelEmbedding7 ∘ raw1287step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1287step0 raw1287step0Labels raw1287step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4491 node4491Labels := by rfl

def raw1288 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw1288Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1288step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw1288step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1288 raw1288Labels = mixedMoment B node1075 node1075Labels := by
  calc
    mixedMoment B raw1288 raw1288Labels = mixedMoment B raw1288step0 raw1288step0Labels := by
      have ha : raw1288step0 = (fun i j => raw1288 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1288step0 raw1288; decide +kernel
      have hl : raw1288step0Labels = raw1288Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1288 raw1288Labels permutation8 permutation4
    _ = mixedMoment B node1075 node1075Labels := by rfl

def raw1289 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![1, 1, -2], ![0, 2, -2]]
def raw1289Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1289step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw1289step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1289step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1289step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1289step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1289step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1289 raw1289Labels = mixedMoment B node1653 node1653Labels := by
  calc
    mixedMoment B raw1289 raw1289Labels = mixedMoment B raw1289step0 raw1289step0Labels := by
      have ha : raw1289step0 = (fun i j => raw1289 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1289step0 raw1289; decide +kernel
      have hl : raw1289step0Labels = raw1289Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1289 raw1289Labels permutation8 permutation6
    mixedMoment B raw1289step0 raw1289step0Labels = mixedMoment B raw1289step1 raw1289step1Labels := by
      have ha : raw1289step1 = -raw1289step0 := by apply Matrix.ext; change ∀ i j, raw1289step1 i j = -(raw1289step0 i j); unfold raw1289step1 raw1289step0; decide +kernel
      have hl : raw1289step1Labels = raw1289step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1289step1 raw1289step1Labels = mixedMoment B raw1289step2 raw1289step2Labels := by
      have ha : raw1289step2 = raw1289step1 := by apply Matrix.ext; unfold raw1289step2 raw1289step1; decide +kernel
      have hl : raw1289step1Labels = labelEmbedding1 ∘ raw1289step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1289step1 raw1289step1Labels raw1289step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1653 node1653Labels := by rfl

def raw1290 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![1, 3, -4]]
def raw1290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1290step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw1290step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1290step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw1290step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1290 raw1290Labels = mixedMoment B node4493 node4493Labels := by
  calc
    mixedMoment B raw1290 raw1290Labels = mixedMoment B raw1290step0 raw1290step0Labels := by
      have ha : raw1290step0 = (fun i j => raw1290 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1290step0 raw1290; decide +kernel
      have hl : raw1290step0Labels = raw1290Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1290 raw1290Labels permutation2 permutation4
    mixedMoment B raw1290step0 raw1290step0Labels = mixedMoment B raw1290step1 raw1290step1Labels := by
      have ha : raw1290step1 = raw1290step0 := by apply Matrix.ext; unfold raw1290step1 raw1290step0; decide +kernel
      have hl : raw1290step0Labels = labelEmbedding7 ∘ raw1290step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1290step0 raw1290step0Labels raw1290step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4493 node4493Labels := by rfl

def raw1291 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![1, 3, -4]]
def raw1291Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1291step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw1291step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1291 raw1291Labels = mixedMoment B node1077 node1077Labels := by
  calc
    mixedMoment B raw1291 raw1291Labels = mixedMoment B raw1291step0 raw1291step0Labels := by
      have ha : raw1291step0 = (fun i j => raw1291 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1291step0 raw1291; decide +kernel
      have hl : raw1291step0Labels = raw1291Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1291 raw1291Labels permutation2 permutation4
    _ = mixedMoment B node1077 node1077Labels := by rfl

def raw1292 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 1, 1], ![1, 3, -4]]
def raw1292Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1292step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw1292step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1292step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![3, 1, -4]]
def raw1292step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1292 raw1292Labels = mixedMoment B node1077 node1077Labels := by
  calc
    mixedMoment B raw1292 raw1292Labels = mixedMoment B raw1292step0 raw1292step0Labels := by
      have ha : raw1292step0 = (fun i j => raw1292 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1292step0 raw1292; decide +kernel
      have hl : raw1292step0Labels = raw1292Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1292 raw1292Labels permutation7 permutation6
    mixedMoment B raw1292step0 raw1292step0Labels = mixedMoment B raw1292step1 raw1292step1Labels := by
      have ha : raw1292step1 = raw1292step0 := by apply Matrix.ext; unfold raw1292step1 raw1292step0; decide +kernel
      have hl : raw1292step0Labels = labelEmbedding1 ∘ raw1292step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1292step0 raw1292step0Labels raw1292step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1077 node1077Labels := by rfl

def raw1293 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw1293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1293step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1293step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1293 raw1293Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw1293 raw1293Labels = mixedMoment B raw1293step0 raw1293step0Labels := by
      have ha : raw1293step0 = (fun i j => raw1293 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1293step0 raw1293; decide +kernel
      have hl : raw1293step0Labels = raw1293Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1293 raw1293Labels permutation32 permutation4
    mixedMoment B raw1293step0 raw1293step0Labels = mixedMoment B raw1293step1 raw1293step1Labels := by
      have ha : raw1293step1 = raw1293step0 := by apply Matrix.ext; unfold raw1293step1 raw1293step0; decide +kernel
      have hl : raw1293step0Labels = labelEmbedding7 ∘ raw1293step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1293step0 raw1293step0Labels raw1293step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw1294 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw1294Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw1294step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1294 raw1294Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw1294 raw1294Labels = mixedMoment B raw1294step0 raw1294step0Labels := by
      have ha : raw1294step0 = (fun i j => raw1294 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1294step0 raw1294; decide +kernel
      have hl : raw1294step0Labels = raw1294Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1294 raw1294Labels permutation32 permutation4
    _ = mixedMoment B node1079 node1079Labels := by rfl

def raw1295 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2]]
def raw1295Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw1295step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1295step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1295step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1295step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1295 raw1295Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw1295 raw1295Labels = mixedMoment B raw1295step0 raw1295step0Labels := by
      have ha : raw1295step0 = (fun i j => raw1295 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1295step0 raw1295; decide +kernel
      have hl : raw1295step0Labels = raw1295Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1295 raw1295Labels permutation32 permutation6
    mixedMoment B raw1295step0 raw1295step0Labels = mixedMoment B raw1295step1 raw1295step1Labels := by
      have ha : raw1295step1 = -raw1295step0 := by apply Matrix.ext; change ∀ i j, raw1295step1 i j = -(raw1295step0 i j); unfold raw1295step1 raw1295step0; decide +kernel
      have hl : raw1295step1Labels = raw1295step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1295step1 raw1295step1Labels = mixedMoment B raw1295step2 raw1295step2Labels := by
      have ha : raw1295step2 = raw1295step1 := by apply Matrix.ext; unfold raw1295step2 raw1295step1; decide +kernel
      have hl : raw1295step1Labels = labelEmbedding1 ∘ raw1295step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1295step1 raw1295step1Labels raw1295step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

def raw1296 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw1296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1296step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw1296step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1296step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw1296step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1296 raw1296Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw1296 raw1296Labels = mixedMoment B raw1296step0 raw1296step0Labels := by
      have ha : raw1296step0 = (fun i j => raw1296 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1296step0 raw1296; decide +kernel
      have hl : raw1296step0Labels = raw1296Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1296 raw1296Labels permutation8 permutation4
    mixedMoment B raw1296step0 raw1296step0Labels = mixedMoment B raw1296step1 raw1296step1Labels := by
      have ha : raw1296step1 = raw1296step0 := by apply Matrix.ext; unfold raw1296step1 raw1296step0; decide +kernel
      have hl : raw1296step0Labels = labelEmbedding7 ∘ raw1296step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1296step0 raw1296step0Labels raw1296step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4496 node4496Labels := by rfl

def raw1297 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw1297Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1297step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw1297step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1297 raw1297Labels = mixedMoment B node1080 node1080Labels := by
  calc
    mixedMoment B raw1297 raw1297Labels = mixedMoment B raw1297step0 raw1297step0Labels := by
      have ha : raw1297step0 = (fun i j => raw1297 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1297step0 raw1297; decide +kernel
      have hl : raw1297step0Labels = raw1297Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1297 raw1297Labels permutation8 permutation4
    _ = mixedMoment B node1080 node1080Labels := by rfl

def raw1298 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 2, -3]]
def raw1298Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1298step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw1298step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw1298step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1298step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw1298step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1298 raw1298Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw1298 raw1298Labels = mixedMoment B raw1298step0 raw1298step0Labels := by
      have ha : raw1298step0 = (fun i j => raw1298 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1298step0 raw1298; decide +kernel
      have hl : raw1298step0Labels = raw1298Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1298 raw1298Labels permutation8 permutation6
    mixedMoment B raw1298step0 raw1298step0Labels = mixedMoment B raw1298step1 raw1298step1Labels := by
      have ha : raw1298step1 = -raw1298step0 := by apply Matrix.ext; change ∀ i j, raw1298step1 i j = -(raw1298step0 i j); unfold raw1298step1 raw1298step0; decide +kernel
      have hl : raw1298step1Labels = raw1298step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1298step1 raw1298step1Labels = mixedMoment B raw1298step2 raw1298step2Labels := by
      have ha : raw1298step2 = raw1298step1 := by apply Matrix.ext; unfold raw1298step2 raw1298step1; decide +kernel
      have hl : raw1298step1Labels = labelEmbedding1 ∘ raw1298step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1298step1 raw1298step1Labels raw1298step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1710 node1710Labels := by rfl

def raw1299 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1299step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1299step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1299step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1299 raw1299Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw1299 raw1299Labels = mixedMoment B raw1299step0 raw1299step0Labels := by
      have ha : raw1299step0 = (fun i j => raw1299 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1299step0 raw1299; decide +kernel
      have hl : raw1299step0Labels = raw1299Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1299 raw1299Labels permutation8 permutation4
    mixedMoment B raw1299step0 raw1299step0Labels = mixedMoment B raw1299step1 raw1299step1Labels := by
      have ha : raw1299step1 = raw1299step0 := by apply Matrix.ext; unfold raw1299step1 raw1299step0; decide +kernel
      have hl : raw1299step0Labels = labelEmbedding7 ∘ raw1299step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1299step0 raw1299step0Labels raw1299step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw1300 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1300Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1300step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw1300step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1300 raw1300Labels = mixedMoment B node1083 node1083Labels := by
  calc
    mixedMoment B raw1300 raw1300Labels = mixedMoment B raw1300step0 raw1300step0Labels := by
      have ha : raw1300step0 = (fun i j => raw1300 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1300step0 raw1300; decide +kernel
      have hl : raw1300step0Labels = raw1300Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1300 raw1300Labels permutation8 permutation4
    _ = mixedMoment B node1083 node1083Labels := by rfl

def raw1301 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![-1, 1, 0], ![1, 1, -2], ![-1, 2, -1]]
def raw1301Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1301step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw1301step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1301step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1301step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw1301step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1301 raw1301Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw1301 raw1301Labels = mixedMoment B raw1301step0 raw1301step0Labels := by
      have ha : raw1301step0 = (fun i j => raw1301 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1301step0 raw1301; decide +kernel
      have hl : raw1301step0Labels = raw1301Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1301 raw1301Labels permutation9 permutation6
    mixedMoment B raw1301step0 raw1301step0Labels = mixedMoment B raw1301step1 raw1301step1Labels := by
      have ha : raw1301step1 = -raw1301step0 := by apply Matrix.ext; change ∀ i j, raw1301step1 i j = -(raw1301step0 i j); unfold raw1301step1 raw1301step0; decide +kernel
      have hl : raw1301step1Labels = raw1301step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1301step1 raw1301step1Labels = mixedMoment B raw1301step2 raw1301step2Labels := by
      have ha : raw1301step2 = raw1301step1 := by apply Matrix.ext; unfold raw1301step2 raw1301step1; decide +kernel
      have hl : raw1301step1Labels = labelEmbedding1 ∘ raw1301step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1301step1 raw1301step1Labels raw1301step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

def raw1302 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1302step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1302step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1302step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1302step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1302 raw1302Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw1302 raw1302Labels = mixedMoment B raw1302step0 raw1302step0Labels := by
      have ha : raw1302step0 = (fun i j => raw1302 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1302step0 raw1302; decide +kernel
      have hl : raw1302step0Labels = raw1302Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1302 raw1302Labels permutation8 permutation4
    mixedMoment B raw1302step0 raw1302step0Labels = mixedMoment B raw1302step1 raw1302step1Labels := by
      have ha : raw1302step1 = raw1302step0 := by apply Matrix.ext; unfold raw1302step1 raw1302step0; decide +kernel
      have hl : raw1302step0Labels = labelEmbedding7 ∘ raw1302step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1302step0 raw1302step0Labels raw1302step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

def raw1303 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1303Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1303step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw1303step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1303 raw1303Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw1303 raw1303Labels = mixedMoment B raw1303step0 raw1303step0Labels := by
      have ha : raw1303step0 = (fun i j => raw1303 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1303step0 raw1303; decide +kernel
      have hl : raw1303step0Labels = raw1303Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1303 raw1303Labels permutation8 permutation4
    _ = mixedMoment B node1087 node1087Labels := by rfl

def raw1304 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, -4, 3], ![0, 1, -1], ![1, 1, -2], ![-2, 2, 0]]
def raw1304Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1304step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw1304step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw1304step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1304step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw1304step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1304 raw1304Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw1304 raw1304Labels = mixedMoment B raw1304step0 raw1304step0Labels := by
      have ha : raw1304step0 = (fun i j => raw1304 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1304step0 raw1304; decide +kernel
      have hl : raw1304step0Labels = raw1304Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1304 raw1304Labels permutation12 permutation6
    mixedMoment B raw1304step0 raw1304step0Labels = mixedMoment B raw1304step1 raw1304step1Labels := by
      have ha : raw1304step1 = -raw1304step0 := by apply Matrix.ext; change ∀ i j, raw1304step1 i j = -(raw1304step0 i j); unfold raw1304step1 raw1304step0; decide +kernel
      have hl : raw1304step1Labels = raw1304step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1304step1 raw1304step1Labels = mixedMoment B raw1304step2 raw1304step2Labels := by
      have ha : raw1304step2 = raw1304step1 := by apply Matrix.ext; unfold raw1304step2 raw1304step1; decide +kernel
      have hl : raw1304step1Labels = labelEmbedding1 ∘ raw1304step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1304step1 raw1304step1Labels raw1304step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1739 node1739Labels := by rfl

def raw1305 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![-2, 3, -1]]
def raw1305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1305step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw1305step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1305step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw1305step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1305 raw1305Labels = mixedMoment B node4507 node4507Labels := by
  calc
    mixedMoment B raw1305 raw1305Labels = mixedMoment B raw1305step0 raw1305step0Labels := by
      have ha : raw1305step0 = (fun i j => raw1305 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1305step0 raw1305; decide +kernel
      have hl : raw1305step0Labels = raw1305Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1305 raw1305Labels permutation2 permutation4
    mixedMoment B raw1305step0 raw1305step0Labels = mixedMoment B raw1305step1 raw1305step1Labels := by
      have ha : raw1305step1 = raw1305step0 := by apply Matrix.ext; unfold raw1305step1 raw1305step0; decide +kernel
      have hl : raw1305step0Labels = labelEmbedding7 ∘ raw1305step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1305step0 raw1305step0Labels raw1305step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4507 node4507Labels := by rfl

def raw1306 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![-2, 3, -1]]
def raw1306Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1306step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw1306step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1306 raw1306Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw1306 raw1306Labels = mixedMoment B raw1306step0 raw1306step0Labels := by
      have ha : raw1306step0 = (fun i j => raw1306 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1306step0 raw1306; decide +kernel
      have hl : raw1306step0Labels = raw1306Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1306 raw1306Labels permutation2 permutation4
    _ = mixedMoment B node1091 node1091Labels := by rfl

def raw1307 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![1, 1, -2], ![-2, 3, -1]]
def raw1307Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1307step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -2, 3], ![-2, 1, 1]]
def raw1307step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1307step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw1307step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1307step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw1307step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1307 raw1307Labels = mixedMoment B node1756 node1756Labels := by
  calc
    mixedMoment B raw1307 raw1307Labels = mixedMoment B raw1307step0 raw1307step0Labels := by
      have ha : raw1307step0 = (fun i j => raw1307 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1307step0 raw1307; decide +kernel
      have hl : raw1307step0Labels = raw1307Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1307 raw1307Labels permutation3 permutation6
    mixedMoment B raw1307step0 raw1307step0Labels = mixedMoment B raw1307step1 raw1307step1Labels := by
      have ha : raw1307step1 = -raw1307step0 := by apply Matrix.ext; change ∀ i j, raw1307step1 i j = -(raw1307step0 i j); unfold raw1307step1 raw1307step0; decide +kernel
      have hl : raw1307step1Labels = raw1307step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1307step1 raw1307step1Labels = mixedMoment B raw1307step2 raw1307step2Labels := by
      have ha : raw1307step2 = raw1307step1 := by apply Matrix.ext; unfold raw1307step2 raw1307step1; decide +kernel
      have hl : raw1307step1Labels = labelEmbedding1 ∘ raw1307step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1307step1 raw1307step1Labels raw1307step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1756 node1756Labels := by rfl

def raw1308 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 2, 0], ![1, 2, -3]]
def raw1308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1308step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw1308step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1308step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw1308step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1308 raw1308Labels = mixedMoment B node4510 node4510Labels := by
  calc
    mixedMoment B raw1308 raw1308Labels = mixedMoment B raw1308step0 raw1308step0Labels := by
      have ha : raw1308step0 = (fun i j => raw1308 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1308step0 raw1308; decide +kernel
      have hl : raw1308step0Labels = raw1308Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1308 raw1308Labels permutation2 permutation4
    mixedMoment B raw1308step0 raw1308step0Labels = mixedMoment B raw1308step1 raw1308step1Labels := by
      have ha : raw1308step1 = raw1308step0 := by apply Matrix.ext; unfold raw1308step1 raw1308step0; decide +kernel
      have hl : raw1308step0Labels = labelEmbedding7 ∘ raw1308step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1308step0 raw1308step0Labels raw1308step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4510 node4510Labels := by rfl

def raw1309 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 2, 0], ![1, 2, -3]]
def raw1309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1309step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw1309step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1309 raw1309Labels = mixedMoment B node1094 node1094Labels := by
  calc
    mixedMoment B raw1309 raw1309Labels = mixedMoment B raw1309step0 raw1309step0Labels := by
      have ha : raw1309step0 = (fun i j => raw1309 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1309step0 raw1309; decide +kernel
      have hl : raw1309step0Labels = raw1309Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1309 raw1309Labels permutation2 permutation4
    _ = mixedMoment B node1094 node1094Labels := by rfl

def raw1310 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, -4, 3], ![-2, 2, 0], ![1, 2, -3]]
def raw1310Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1310step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-3, 1, 2]]
def raw1310step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1310step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw1310step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1310step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw1310step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1310 raw1310Labels = mixedMoment B node1741 node1741Labels := by
  calc
    mixedMoment B raw1310 raw1310Labels = mixedMoment B raw1310step0 raw1310step0Labels := by
      have ha : raw1310step0 = (fun i j => raw1310 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1310step0 raw1310; decide +kernel
      have hl : raw1310step0Labels = raw1310Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1310 raw1310Labels permutation2 permutation6
    mixedMoment B raw1310step0 raw1310step0Labels = mixedMoment B raw1310step1 raw1310step1Labels := by
      have ha : raw1310step1 = -raw1310step0 := by apply Matrix.ext; change ∀ i j, raw1310step1 i j = -(raw1310step0 i j); unfold raw1310step1 raw1310step0; decide +kernel
      have hl : raw1310step1Labels = raw1310step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1310step1 raw1310step1Labels = mixedMoment B raw1310step2 raw1310step2Labels := by
      have ha : raw1310step2 = raw1310step1 := by apply Matrix.ext; unfold raw1310step2 raw1310step1; decide +kernel
      have hl : raw1310step1Labels = labelEmbedding1 ∘ raw1310step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1310step1 raw1310step1Labels raw1310step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1741 node1741Labels := by rfl

def raw1311 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1311step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1311step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1311step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1311 raw1311Labels = mixedMoment B node4513 node4513Labels := by
  calc
    mixedMoment B raw1311 raw1311Labels = mixedMoment B raw1311step0 raw1311step0Labels := by
      have ha : raw1311step0 = (fun i j => raw1311 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1311step0 raw1311; decide +kernel
      have hl : raw1311step0Labels = raw1311Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1311 raw1311Labels permutation152 permutation4
    mixedMoment B raw1311step0 raw1311step0Labels = mixedMoment B raw1311step1 raw1311step1Labels := by
      have ha : raw1311step1 = raw1311step0 := by apply Matrix.ext; unfold raw1311step1 raw1311step0; decide +kernel
      have hl : raw1311step0Labels = labelEmbedding7 ∘ raw1311step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1311step0 raw1311step0Labels raw1311step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4513 node4513Labels := by rfl

def raw1312 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1312 raw1312Labels = mixedMoment B node1097 node1097Labels := by
  calc
    mixedMoment B raw1312 raw1312Labels = mixedMoment B raw1312step0 raw1312step0Labels := by
      have ha : raw1312step0 = (fun i j => raw1312 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1312step0 raw1312; decide +kernel
      have hl : raw1312step0Labels = raw1312Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1312 raw1312Labels permutation152 permutation4
    _ = mixedMoment B node1097 node1097Labels := by rfl

def raw1313 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1313Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1313step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1313step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1313step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1313step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1313step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1313step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1313 raw1313Labels = mixedMoment B node3232 node3232Labels := by
  calc
    mixedMoment B raw1313 raw1313Labels = mixedMoment B raw1313step0 raw1313step0Labels := by
      have ha : raw1313step0 = (fun i j => raw1313 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1313step0 raw1313; decide +kernel
      have hl : raw1313step0Labels = raw1313Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1313 raw1313Labels permutation152 permutation6
    mixedMoment B raw1313step0 raw1313step0Labels = mixedMoment B raw1313step1 raw1313step1Labels := by
      have ha : raw1313step1 = -raw1313step0 := by apply Matrix.ext; change ∀ i j, raw1313step1 i j = -(raw1313step0 i j); unfold raw1313step1 raw1313step0; decide +kernel
      have hl : raw1313step1Labels = raw1313step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1313step1 raw1313step1Labels = mixedMoment B raw1313step2 raw1313step2Labels := by
      have ha : raw1313step2 = raw1313step1 := by apply Matrix.ext; unfold raw1313step2 raw1313step1; decide +kernel
      have hl : raw1313step1Labels = labelEmbedding1 ∘ raw1313step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1313step1 raw1313step1Labels raw1313step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3232 node3232Labels := by rfl

def raw1314 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1314step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1314step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1314 raw1314Labels = mixedMoment B node4514 node4514Labels := by
  calc
    mixedMoment B raw1314 raw1314Labels = mixedMoment B raw1314step0 raw1314step0Labels := by
      have ha : raw1314step0 = (fun i j => raw1314 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1314step0 raw1314; decide +kernel
      have hl : raw1314step0Labels = raw1314Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1314 raw1314Labels permutation32 permutation4
    mixedMoment B raw1314step0 raw1314step0Labels = mixedMoment B raw1314step1 raw1314step1Labels := by
      have ha : raw1314step1 = raw1314step0 := by apply Matrix.ext; unfold raw1314step1 raw1314step0; decide +kernel
      have hl : raw1314step0Labels = labelEmbedding7 ∘ raw1314step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1314step0 raw1314step0Labels raw1314step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4514 node4514Labels := by rfl

def raw1315 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1315step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1315 raw1315Labels = mixedMoment B node1098 node1098Labels := by
  calc
    mixedMoment B raw1315 raw1315Labels = mixedMoment B raw1315step0 raw1315step0Labels := by
      have ha : raw1315step0 = (fun i j => raw1315 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1315step0 raw1315; decide +kernel
      have hl : raw1315step0Labels = raw1315Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1315 raw1315Labels permutation32 permutation4
    _ = mixedMoment B node1098 node1098Labels := by rfl

def raw1316 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1316Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 2, -4]]
def raw1316step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 2, -4]]
def raw1316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1316 raw1316Labels = mixedMoment B node1894 node1894Labels := by
  calc
    mixedMoment B raw1316 raw1316Labels = mixedMoment B raw1316step0 raw1316step0Labels := by
      have ha : raw1316step0 = (fun i j => raw1316 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1316step0 raw1316; decide +kernel
      have hl : raw1316step0Labels = raw1316Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1316 raw1316Labels permutation151 permutation6
    mixedMoment B raw1316step0 raw1316step0Labels = mixedMoment B raw1316step1 raw1316step1Labels := by
      have ha : raw1316step1 = raw1316step0 := by apply Matrix.ext; unfold raw1316step1 raw1316step0; decide +kernel
      have hl : raw1316step0Labels = labelEmbedding1 ∘ raw1316step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1316step0 raw1316step0Labels raw1316step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1894 node1894Labels := by rfl

def raw1317 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1317step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1317step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1317 raw1317Labels = mixedMoment B node4515 node4515Labels := by
  calc
    mixedMoment B raw1317 raw1317Labels = mixedMoment B raw1317step0 raw1317step0Labels := by
      have ha : raw1317step0 = (fun i j => raw1317 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1317step0 raw1317; decide +kernel
      have hl : raw1317step0Labels = raw1317Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1317 raw1317Labels permutation32 permutation4
    mixedMoment B raw1317step0 raw1317step0Labels = mixedMoment B raw1317step1 raw1317step1Labels := by
      have ha : raw1317step1 = raw1317step0 := by apply Matrix.ext; unfold raw1317step1 raw1317step0; decide +kernel
      have hl : raw1317step0Labels = labelEmbedding7 ∘ raw1317step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1317step0 raw1317step0Labels raw1317step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4515 node4515Labels := by rfl

def raw1318 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1318step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1318 raw1318Labels = mixedMoment B node1099 node1099Labels := by
  calc
    mixedMoment B raw1318 raw1318Labels = mixedMoment B raw1318step0 raw1318step0Labels := by
      have ha : raw1318step0 = (fun i j => raw1318 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1318step0 raw1318; decide +kernel
      have hl : raw1318step0Labels = raw1318Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1318 raw1318Labels permutation32 permutation4
    _ = mixedMoment B node1099 node1099Labels := by rfl

def raw1319 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1319Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -1, -1], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw1319step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1319step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1319step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1319step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1319 raw1319Labels = mixedMoment B node3233 node3233Labels := by
  calc
    mixedMoment B raw1319 raw1319Labels = mixedMoment B raw1319step0 raw1319step0Labels := by
      have ha : raw1319step0 = (fun i j => raw1319 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1319step0 raw1319; decide +kernel
      have hl : raw1319step0Labels = raw1319Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1319 raw1319Labels permutation32 permutation6
    mixedMoment B raw1319step0 raw1319step0Labels = mixedMoment B raw1319step1 raw1319step1Labels := by
      have ha : raw1319step1 = -raw1319step0 := by apply Matrix.ext; change ∀ i j, raw1319step1 i j = -(raw1319step0 i j); unfold raw1319step1 raw1319step0; decide +kernel
      have hl : raw1319step1Labels = raw1319step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1319step1 raw1319step1Labels = mixedMoment B raw1319step2 raw1319step2Labels := by
      have ha : raw1319step2 = raw1319step1 := by apply Matrix.ext; unfold raw1319step2 raw1319step1; decide +kernel
      have hl : raw1319step1Labels = labelEmbedding1 ∘ raw1319step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1319step1 raw1319step1Labels raw1319step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3233 node3233Labels := by rfl

def raw1320 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1320step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1320step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1320 raw1320Labels = mixedMoment B node4516 node4516Labels := by
  calc
    mixedMoment B raw1320 raw1320Labels = mixedMoment B raw1320step0 raw1320step0Labels := by
      have ha : raw1320step0 = (fun i j => raw1320 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1320step0 raw1320; decide +kernel
      have hl : raw1320step0Labels = raw1320Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1320 raw1320Labels permutation152 permutation4
    mixedMoment B raw1320step0 raw1320step0Labels = mixedMoment B raw1320step1 raw1320step1Labels := by
      have ha : raw1320step1 = raw1320step0 := by apply Matrix.ext; unfold raw1320step1 raw1320step0; decide +kernel
      have hl : raw1320step0Labels = labelEmbedding7 ∘ raw1320step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1320step0 raw1320step0Labels raw1320step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4516 node4516Labels := by rfl

def raw1321 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1321step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1321 raw1321Labels = mixedMoment B node1100 node1100Labels := by
  calc
    mixedMoment B raw1321 raw1321Labels = mixedMoment B raw1321step0 raw1321step0Labels := by
      have ha : raw1321step0 = (fun i j => raw1321 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1321step0 raw1321; decide +kernel
      have hl : raw1321step0Labels = raw1321Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1321 raw1321Labels permutation152 permutation4
    _ = mixedMoment B node1100 node1100Labels := by rfl

def raw1322 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1322Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw1322step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1322step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1322step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1322step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1322 raw1322Labels = mixedMoment B node3234 node3234Labels := by
  calc
    mixedMoment B raw1322 raw1322Labels = mixedMoment B raw1322step0 raw1322step0Labels := by
      have ha : raw1322step0 = (fun i j => raw1322 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1322step0 raw1322; decide +kernel
      have hl : raw1322step0Labels = raw1322Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1322 raw1322Labels permutation152 permutation6
    mixedMoment B raw1322step0 raw1322step0Labels = mixedMoment B raw1322step1 raw1322step1Labels := by
      have ha : raw1322step1 = -raw1322step0 := by apply Matrix.ext; change ∀ i j, raw1322step1 i j = -(raw1322step0 i j); unfold raw1322step1 raw1322step0; decide +kernel
      have hl : raw1322step1Labels = raw1322step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1322step1 raw1322step1Labels = mixedMoment B raw1322step2 raw1322step2Labels := by
      have ha : raw1322step2 = raw1322step1 := by apply Matrix.ext; unfold raw1322step2 raw1322step1; decide +kernel
      have hl : raw1322step1Labels = labelEmbedding1 ∘ raw1322step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1322step1 raw1322step1Labels raw1322step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3234 node3234Labels := by rfl

def raw1323 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1323step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1323step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1323step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1323 raw1323Labels = mixedMoment B node4517 node4517Labels := by
  calc
    mixedMoment B raw1323 raw1323Labels = mixedMoment B raw1323step0 raw1323step0Labels := by
      have ha : raw1323step0 = (fun i j => raw1323 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1323step0 raw1323; decide +kernel
      have hl : raw1323step0Labels = raw1323Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1323 raw1323Labels permutation32 permutation4
    mixedMoment B raw1323step0 raw1323step0Labels = mixedMoment B raw1323step1 raw1323step1Labels := by
      have ha : raw1323step1 = raw1323step0 := by apply Matrix.ext; unfold raw1323step1 raw1323step0; decide +kernel
      have hl : raw1323step0Labels = labelEmbedding7 ∘ raw1323step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1323step0 raw1323step0Labels raw1323step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4517 node4517Labels := by rfl

def raw1324 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1324Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1324step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1324 raw1324Labels = mixedMoment B node1101 node1101Labels := by
  calc
    mixedMoment B raw1324 raw1324Labels = mixedMoment B raw1324step0 raw1324step0Labels := by
      have ha : raw1324step0 = (fun i j => raw1324 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1324step0 raw1324; decide +kernel
      have hl : raw1324step0Labels = raw1324Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1324 raw1324Labels permutation32 permutation4
    _ = mixedMoment B node1101 node1101Labels := by rfl

def raw1325 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1325Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1325step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1325step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1325step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1325step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1325 raw1325Labels = mixedMoment B node3235 node3235Labels := by
  calc
    mixedMoment B raw1325 raw1325Labels = mixedMoment B raw1325step0 raw1325step0Labels := by
      have ha : raw1325step0 = (fun i j => raw1325 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1325step0 raw1325; decide +kernel
      have hl : raw1325step0Labels = raw1325Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1325 raw1325Labels permutation32 permutation6
    mixedMoment B raw1325step0 raw1325step0Labels = mixedMoment B raw1325step1 raw1325step1Labels := by
      have ha : raw1325step1 = -raw1325step0 := by apply Matrix.ext; change ∀ i j, raw1325step1 i j = -(raw1325step0 i j); unfold raw1325step1 raw1325step0; decide +kernel
      have hl : raw1325step1Labels = raw1325step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1325step1 raw1325step1Labels = mixedMoment B raw1325step2 raw1325step2Labels := by
      have ha : raw1325step2 = raw1325step1 := by apply Matrix.ext; unfold raw1325step2 raw1325step1; decide +kernel
      have hl : raw1325step1Labels = labelEmbedding1 ∘ raw1325step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1325step1 raw1325step1Labels raw1325step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3235 node3235Labels := by rfl

def raw1326 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1326step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1326step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1326 raw1326Labels = mixedMoment B node4518 node4518Labels := by
  calc
    mixedMoment B raw1326 raw1326Labels = mixedMoment B raw1326step0 raw1326step0Labels := by
      have ha : raw1326step0 = (fun i j => raw1326 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1326step0 raw1326; decide +kernel
      have hl : raw1326step0Labels = raw1326Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1326 raw1326Labels permutation32 permutation4
    mixedMoment B raw1326step0 raw1326step0Labels = mixedMoment B raw1326step1 raw1326step1Labels := by
      have ha : raw1326step1 = raw1326step0 := by apply Matrix.ext; unfold raw1326step1 raw1326step0; decide +kernel
      have hl : raw1326step0Labels = labelEmbedding7 ∘ raw1326step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1326step0 raw1326step0Labels raw1326step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4518 node4518Labels := by rfl

def raw1327 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1327Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1327step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1327 raw1327Labels = mixedMoment B node1102 node1102Labels := by
  calc
    mixedMoment B raw1327 raw1327Labels = mixedMoment B raw1327step0 raw1327step0Labels := by
      have ha : raw1327step0 = (fun i j => raw1327 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1327step0 raw1327; decide +kernel
      have hl : raw1327step0Labels = raw1327Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1327 raw1327Labels permutation32 permutation4
    _ = mixedMoment B node1102 node1102Labels := by rfl

def raw1328 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1328Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1328step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1328step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1328step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1328step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1328 raw1328Labels = mixedMoment B node3236 node3236Labels := by
  calc
    mixedMoment B raw1328 raw1328Labels = mixedMoment B raw1328step0 raw1328step0Labels := by
      have ha : raw1328step0 = (fun i j => raw1328 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1328step0 raw1328; decide +kernel
      have hl : raw1328step0Labels = raw1328Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1328 raw1328Labels permutation32 permutation6
    mixedMoment B raw1328step0 raw1328step0Labels = mixedMoment B raw1328step1 raw1328step1Labels := by
      have ha : raw1328step1 = -raw1328step0 := by apply Matrix.ext; change ∀ i j, raw1328step1 i j = -(raw1328step0 i j); unfold raw1328step1 raw1328step0; decide +kernel
      have hl : raw1328step1Labels = raw1328step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1328step1 raw1328step1Labels = mixedMoment B raw1328step2 raw1328step2Labels := by
      have ha : raw1328step2 = raw1328step1 := by apply Matrix.ext; unfold raw1328step2 raw1328step1; decide +kernel
      have hl : raw1328step1Labels = labelEmbedding1 ∘ raw1328step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1328step1 raw1328step1Labels raw1328step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3236 node3236Labels := by rfl

def raw1329 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 2, -1], ![0, 3, -3]]
def raw1329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1329step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw1329step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw1329step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1329 raw1329Labels = mixedMoment B node4519 node4519Labels := by
  calc
    mixedMoment B raw1329 raw1329Labels = mixedMoment B raw1329step0 raw1329step0Labels := by
      have ha : raw1329step0 = (fun i j => raw1329 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1329step0 raw1329; decide +kernel
      have hl : raw1329step0Labels = raw1329Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1329 raw1329Labels permutation8 permutation4
    mixedMoment B raw1329step0 raw1329step0Labels = mixedMoment B raw1329step1 raw1329step1Labels := by
      have ha : raw1329step1 = raw1329step0 := by apply Matrix.ext; unfold raw1329step1 raw1329step0; decide +kernel
      have hl : raw1329step0Labels = labelEmbedding7 ∘ raw1329step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1329step0 raw1329step0Labels raw1329step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4519 node4519Labels := by rfl

def raw1330 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 2, -1], ![0, 3, -3]]
def raw1330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1330step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw1330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1330 raw1330Labels = mixedMoment B node1103 node1103Labels := by
  calc
    mixedMoment B raw1330 raw1330Labels = mixedMoment B raw1330step0 raw1330step0Labels := by
      have ha : raw1330step0 = (fun i j => raw1330 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1330step0 raw1330; decide +kernel
      have hl : raw1330step0Labels = raw1330Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1330 raw1330Labels permutation8 permutation4
    _ = mixedMoment B node1103 node1103Labels := by rfl

def raw1331 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![-1, 2, -1], ![0, 3, -3]]
def raw1331Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1331step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![2, -1, -1], ![2, 2, -4]]
def raw1331step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1331step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![2, -1, -1], ![2, 2, -4]]
def raw1331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1331 raw1331Labels = mixedMoment B node1858 node1858Labels := by
  calc
    mixedMoment B raw1331 raw1331Labels = mixedMoment B raw1331step0 raw1331step0Labels := by
      have ha : raw1331step0 = (fun i j => raw1331 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1331step0 raw1331; decide +kernel
      have hl : raw1331step0Labels = raw1331Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1331 raw1331Labels permutation31 permutation6
    mixedMoment B raw1331step0 raw1331step0Labels = mixedMoment B raw1331step1 raw1331step1Labels := by
      have ha : raw1331step1 = raw1331step0 := by apply Matrix.ext; unfold raw1331step1 raw1331step0; decide +kernel
      have hl : raw1331step0Labels = labelEmbedding1 ∘ raw1331step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1331step0 raw1331step0Labels raw1331step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1858 node1858Labels := by rfl

def raw1332 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 2, -2], ![-1, 3, -2]]
def raw1332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1332step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw1332step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw1332step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1332 raw1332Labels = mixedMoment B node4520 node4520Labels := by
  calc
    mixedMoment B raw1332 raw1332Labels = mixedMoment B raw1332step0 raw1332step0Labels := by
      have ha : raw1332step0 = (fun i j => raw1332 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1332step0 raw1332; decide +kernel
      have hl : raw1332step0Labels = raw1332Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1332 raw1332Labels permutation8 permutation4
    mixedMoment B raw1332step0 raw1332step0Labels = mixedMoment B raw1332step1 raw1332step1Labels := by
      have ha : raw1332step1 = raw1332step0 := by apply Matrix.ext; unfold raw1332step1 raw1332step0; decide +kernel
      have hl : raw1332step0Labels = labelEmbedding7 ∘ raw1332step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1332step0 raw1332step0Labels raw1332step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4520 node4520Labels := by rfl

def raw1333 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 2, -2], ![-1, 3, -2]]
def raw1333Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1333step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, 0, -2], ![3, -1, -2]]
def raw1333step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1333 raw1333Labels = mixedMoment B node1104 node1104Labels := by
  calc
    mixedMoment B raw1333 raw1333Labels = mixedMoment B raw1333step0 raw1333step0Labels := by
      have ha : raw1333step0 = (fun i j => raw1333 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1333step0 raw1333; decide +kernel
      have hl : raw1333step0Labels = raw1333Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1333 raw1333Labels permutation8 permutation4
    _ = mixedMoment B node1104 node1104Labels := by rfl

def raw1334 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-1, -1, 2], ![0, 2, -2], ![-1, 3, -2]]
def raw1334Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1334step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![2, -1, -1], ![-2, 0, 2], ![-2, -1, 3]]
def raw1334step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw1334step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1334step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw1334step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1334 raw1334Labels = mixedMoment B node3237 node3237Labels := by
  calc
    mixedMoment B raw1334 raw1334Labels = mixedMoment B raw1334step0 raw1334step0Labels := by
      have ha : raw1334step0 = (fun i j => raw1334 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1334step0 raw1334; decide +kernel
      have hl : raw1334step0Labels = raw1334Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1334 raw1334Labels permutation8 permutation6
    mixedMoment B raw1334step0 raw1334step0Labels = mixedMoment B raw1334step1 raw1334step1Labels := by
      have ha : raw1334step1 = -raw1334step0 := by apply Matrix.ext; change ∀ i j, raw1334step1 i j = -(raw1334step0 i j); unfold raw1334step1 raw1334step0; decide +kernel
      have hl : raw1334step1Labels = raw1334step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1334step1 raw1334step1Labels = mixedMoment B raw1334step2 raw1334step2Labels := by
      have ha : raw1334step2 = raw1334step1 := by apply Matrix.ext; unfold raw1334step2 raw1334step1; decide +kernel
      have hl : raw1334step1Labels = labelEmbedding1 ∘ raw1334step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1334step1 raw1334step1Labels raw1334step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3237 node3237Labels := by rfl

def raw1335 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1335step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1335step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1335step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1335 raw1335Labels = mixedMoment B node4521 node4521Labels := by
  calc
    mixedMoment B raw1335 raw1335Labels = mixedMoment B raw1335step0 raw1335step0Labels := by
      have ha : raw1335step0 = (fun i j => raw1335 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1335step0 raw1335; decide +kernel
      have hl : raw1335step0Labels = raw1335Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1335 raw1335Labels permutation152 permutation4
    mixedMoment B raw1335step0 raw1335step0Labels = mixedMoment B raw1335step1 raw1335step1Labels := by
      have ha : raw1335step1 = raw1335step0 := by apply Matrix.ext; unfold raw1335step1 raw1335step0; decide +kernel
      have hl : raw1335step0Labels = labelEmbedding7 ∘ raw1335step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1335step0 raw1335step0Labels raw1335step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4521 node4521Labels := by rfl

def raw1336 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw1336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1336 raw1336Labels = mixedMoment B node1105 node1105Labels := by
  calc
    mixedMoment B raw1336 raw1336Labels = mixedMoment B raw1336step0 raw1336step0Labels := by
      have ha : raw1336step0 = (fun i j => raw1336 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1336step0 raw1336; decide +kernel
      have hl : raw1336step0Labels = raw1336Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1336 raw1336Labels permutation152 permutation4
    _ = mixedMoment B node1105 node1105Labels := by rfl

def raw1337 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 3, -3]]
def raw1337Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw1337step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1337step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw1337step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1337 raw1337Labels = mixedMoment B node1887 node1887Labels := by
  calc
    mixedMoment B raw1337 raw1337Labels = mixedMoment B raw1337step0 raw1337step0Labels := by
      have ha : raw1337step0 = (fun i j => raw1337 (permutation688 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1337step0 raw1337; decide +kernel
      have hl : raw1337step0Labels = raw1337Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1337 raw1337Labels permutation688 permutation6
    mixedMoment B raw1337step0 raw1337step0Labels = mixedMoment B raw1337step1 raw1337step1Labels := by
      have ha : raw1337step1 = raw1337step0 := by apply Matrix.ext; unfold raw1337step1 raw1337step0; decide +kernel
      have hl : raw1337step0Labels = labelEmbedding1 ∘ raw1337step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1337step0 raw1337step0Labels raw1337step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1887 node1887Labels := by rfl

def raw1338 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1338step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1338step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1338 raw1338Labels = mixedMoment B node4522 node4522Labels := by
  calc
    mixedMoment B raw1338 raw1338Labels = mixedMoment B raw1338step0 raw1338step0Labels := by
      have ha : raw1338step0 = (fun i j => raw1338 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1338step0 raw1338; decide +kernel
      have hl : raw1338step0Labels = raw1338Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1338 raw1338Labels permutation152 permutation4
    mixedMoment B raw1338step0 raw1338step0Labels = mixedMoment B raw1338step1 raw1338step1Labels := by
      have ha : raw1338step1 = raw1338step0 := by apply Matrix.ext; unfold raw1338step1 raw1338step0; decide +kernel
      have hl : raw1338step0Labels = labelEmbedding7 ∘ raw1338step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1338step0 raw1338step0Labels raw1338step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4522 node4522Labels := by rfl

def raw1339 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw1339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1339 raw1339Labels = mixedMoment B node1106 node1106Labels := by
  calc
    mixedMoment B raw1339 raw1339Labels = mixedMoment B raw1339step0 raw1339step0Labels := by
      have ha : raw1339step0 = (fun i j => raw1339 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1339step0 raw1339; decide +kernel
      have hl : raw1339step0Labels = raw1339Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1339 raw1339Labels permutation152 permutation4
    _ = mixedMoment B node1106 node1106Labels := by rfl

def raw1340 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![0, 2, -2]]
def raw1340Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw1340step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1340step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1340step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1340step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1340step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1340 raw1340Labels = mixedMoment B node3249 node3249Labels := by
  calc
    mixedMoment B raw1340 raw1340Labels = mixedMoment B raw1340step0 raw1340step0Labels := by
      have ha : raw1340step0 = (fun i j => raw1340 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1340step0 raw1340; decide +kernel
      have hl : raw1340step0Labels = raw1340Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1340 raw1340Labels permutation152 permutation6
    mixedMoment B raw1340step0 raw1340step0Labels = mixedMoment B raw1340step1 raw1340step1Labels := by
      have ha : raw1340step1 = -raw1340step0 := by apply Matrix.ext; change ∀ i j, raw1340step1 i j = -(raw1340step0 i j); unfold raw1340step1 raw1340step0; decide +kernel
      have hl : raw1340step1Labels = raw1340step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1340step1 raw1340step1Labels = mixedMoment B raw1340step2 raw1340step2Labels := by
      have ha : raw1340step2 = raw1340step1 := by apply Matrix.ext; unfold raw1340step2 raw1340step1; decide +kernel
      have hl : raw1340step1Labels = labelEmbedding1 ∘ raw1340step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1340step1 raw1340step1Labels raw1340step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3249 node3249Labels := by rfl

def raw1341 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1341step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1341step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1341step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1341 raw1341Labels = mixedMoment B node4523 node4523Labels := by
  calc
    mixedMoment B raw1341 raw1341Labels = mixedMoment B raw1341step0 raw1341step0Labels := by
      have ha : raw1341step0 = (fun i j => raw1341 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1341step0 raw1341; decide +kernel
      have hl : raw1341step0Labels = raw1341Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1341 raw1341Labels permutation152 permutation4
    mixedMoment B raw1341step0 raw1341step0Labels = mixedMoment B raw1341step1 raw1341step1Labels := by
      have ha : raw1341step1 = raw1341step0 := by apply Matrix.ext; unfold raw1341step1 raw1341step0; decide +kernel
      have hl : raw1341step0Labels = labelEmbedding7 ∘ raw1341step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1341step0 raw1341step0Labels raw1341step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4523 node4523Labels := by rfl

def raw1342 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1342Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1342step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw1342step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1342 raw1342Labels = mixedMoment B node1107 node1107Labels := by
  calc
    mixedMoment B raw1342 raw1342Labels = mixedMoment B raw1342step0 raw1342step0Labels := by
      have ha : raw1342step0 = (fun i j => raw1342 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1342step0 raw1342; decide +kernel
      have hl : raw1342step0Labels = raw1342Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1342 raw1342Labels permutation152 permutation4
    _ = mixedMoment B node1107 node1107Labels := by rfl

def raw1343 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![-1, 3, -2]]
def raw1343Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1343step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1343step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1343step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1343step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1343step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1343 raw1343Labels = mixedMoment B node3250 node3250Labels := by
  calc
    mixedMoment B raw1343 raw1343Labels = mixedMoment B raw1343step0 raw1343step0Labels := by
      have ha : raw1343step0 = (fun i j => raw1343 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1343step0 raw1343; decide +kernel
      have hl : raw1343step0Labels = raw1343Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1343 raw1343Labels permutation152 permutation6
    mixedMoment B raw1343step0 raw1343step0Labels = mixedMoment B raw1343step1 raw1343step1Labels := by
      have ha : raw1343step1 = -raw1343step0 := by apply Matrix.ext; change ∀ i j, raw1343step1 i j = -(raw1343step0 i j); unfold raw1343step1 raw1343step0; decide +kernel
      have hl : raw1343step1Labels = raw1343step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1343step1 raw1343step1Labels = mixedMoment B raw1343step2 raw1343step2Labels := by
      have ha : raw1343step2 = raw1343step1 := by apply Matrix.ext; unfold raw1343step2 raw1343step1; decide +kernel
      have hl : raw1343step1Labels = labelEmbedding1 ∘ raw1343step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1343step1 raw1343step1Labels raw1343step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3250 node3250Labels := by rfl

def raw1344 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1344step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1344step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1344step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1344step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1344 raw1344Labels = mixedMoment B node4524 node4524Labels := by
  calc
    mixedMoment B raw1344 raw1344Labels = mixedMoment B raw1344step0 raw1344step0Labels := by
      have ha : raw1344step0 = (fun i j => raw1344 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1344step0 raw1344; decide +kernel
      have hl : raw1344step0Labels = raw1344Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1344 raw1344Labels permutation152 permutation4
    mixedMoment B raw1344step0 raw1344step0Labels = mixedMoment B raw1344step1 raw1344step1Labels := by
      have ha : raw1344step1 = raw1344step0 := by apply Matrix.ext; unfold raw1344step1 raw1344step0; decide +kernel
      have hl : raw1344step0Labels = labelEmbedding7 ∘ raw1344step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1344step0 raw1344step0Labels raw1344step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4524 node4524Labels := by rfl

def raw1345 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1345step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw1345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1345 raw1345Labels = mixedMoment B node1108 node1108Labels := by
  calc
    mixedMoment B raw1345 raw1345Labels = mixedMoment B raw1345step0 raw1345step0Labels := by
      have ha : raw1345step0 = (fun i j => raw1345 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1345step0 raw1345; decide +kernel
      have hl : raw1345step0Labels = raw1345Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1345 raw1345Labels permutation152 permutation4
    _ = mixedMoment B node1108 node1108Labels := by rfl

def raw1346 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![0, 2, -2]]
def raw1346Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1346step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1346step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1346step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1346step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1346step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1346 raw1346Labels = mixedMoment B node3251 node3251Labels := by
  calc
    mixedMoment B raw1346 raw1346Labels = mixedMoment B raw1346step0 raw1346step0Labels := by
      have ha : raw1346step0 = (fun i j => raw1346 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1346step0 raw1346; decide +kernel
      have hl : raw1346step0Labels = raw1346Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1346 raw1346Labels permutation152 permutation6
    mixedMoment B raw1346step0 raw1346step0Labels = mixedMoment B raw1346step1 raw1346step1Labels := by
      have ha : raw1346step1 = -raw1346step0 := by apply Matrix.ext; change ∀ i j, raw1346step1 i j = -(raw1346step0 i j); unfold raw1346step1 raw1346step0; decide +kernel
      have hl : raw1346step1Labels = raw1346step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1346step1 raw1346step1Labels = mixedMoment B raw1346step2 raw1346step2Labels := by
      have ha : raw1346step2 = raw1346step1 := by apply Matrix.ext; unfold raw1346step2 raw1346step1; decide +kernel
      have hl : raw1346step1Labels = labelEmbedding1 ∘ raw1346step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1346step1 raw1346step1Labels raw1346step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3251 node3251Labels := by rfl

def raw1347 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 3, -3]]
def raw1347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw1347step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw1347step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1347 raw1347Labels = mixedMoment B node4525 node4525Labels := by
  calc
    mixedMoment B raw1347 raw1347Labels = mixedMoment B raw1347step0 raw1347step0Labels := by
      have ha : raw1347step0 = (fun i j => raw1347 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1347step0 raw1347; decide +kernel
      have hl : raw1347step0Labels = raw1347Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1347 raw1347Labels permutation32 permutation4
    mixedMoment B raw1347step0 raw1347step0Labels = mixedMoment B raw1347step1 raw1347step1Labels := by
      have ha : raw1347step1 = raw1347step0 := by apply Matrix.ext; unfold raw1347step1 raw1347step0; decide +kernel
      have hl : raw1347step0Labels = labelEmbedding7 ∘ raw1347step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1347step0 raw1347step0Labels raw1347step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4525 node4525Labels := by rfl

def raw1348 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 3, -3]]
def raw1348Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw1348step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1348 raw1348Labels = mixedMoment B node1109 node1109Labels := by
  calc
    mixedMoment B raw1348 raw1348Labels = mixedMoment B raw1348step0 raw1348step0Labels := by
      have ha : raw1348step0 = (fun i j => raw1348 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1348step0 raw1348; decide +kernel
      have hl : raw1348step0Labels = raw1348Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1348 raw1348Labels permutation32 permutation4
    _ = mixedMoment B node1109 node1109Labels := by rfl

def raw1349 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 3, -3]]
def raw1349Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw1349step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw1349step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1349 raw1349Labels = mixedMoment B node1849 node1849Labels := by
  calc
    mixedMoment B raw1349 raw1349Labels = mixedMoment B raw1349step0 raw1349step0Labels := by
      have ha : raw1349step0 = (fun i j => raw1349 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1349step0 raw1349; decide +kernel
      have hl : raw1349step0Labels = raw1349Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1349 raw1349Labels permutation151 permutation6
    mixedMoment B raw1349step0 raw1349step0Labels = mixedMoment B raw1349step1 raw1349step1Labels := by
      have ha : raw1349step1 = raw1349step0 := by apply Matrix.ext; unfold raw1349step1 raw1349step0; decide +kernel
      have hl : raw1349step0Labels = labelEmbedding1 ∘ raw1349step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1349step0 raw1349step0Labels raw1349step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1849 node1849Labels := by rfl

def raw1350 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw1350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw1350step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw1350step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1350 raw1350Labels = mixedMoment B node4526 node4526Labels := by
  calc
    mixedMoment B raw1350 raw1350Labels = mixedMoment B raw1350step0 raw1350step0Labels := by
      have ha : raw1350step0 = (fun i j => raw1350 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1350step0 raw1350; decide +kernel
      have hl : raw1350step0Labels = raw1350Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1350 raw1350Labels permutation32 permutation4
    mixedMoment B raw1350step0 raw1350step0Labels = mixedMoment B raw1350step1 raw1350step1Labels := by
      have ha : raw1350step1 = raw1350step0 := by apply Matrix.ext; unfold raw1350step1 raw1350step0; decide +kernel
      have hl : raw1350step0Labels = labelEmbedding7 ∘ raw1350step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1350step0 raw1350step0Labels raw1350step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4526 node4526Labels := by rfl

def raw1351 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw1351Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw1351step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1351 raw1351Labels = mixedMoment B node1110 node1110Labels := by
  calc
    mixedMoment B raw1351 raw1351Labels = mixedMoment B raw1351step0 raw1351step0Labels := by
      have ha : raw1351step0 = (fun i j => raw1351 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1351step0 raw1351; decide +kernel
      have hl : raw1351step0Labels = raw1351Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1351 raw1351Labels permutation32 permutation4
    _ = mixedMoment B node1110 node1110Labels := by rfl

def raw1352 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 0, 1], ![0, 2, -2], ![-1, 3, -2]]
def raw1352Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, -1, 3]]
def raw1352step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw1352step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1352step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw1352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1352 raw1352Labels = mixedMoment B node3252 node3252Labels := by
  calc
    mixedMoment B raw1352 raw1352Labels = mixedMoment B raw1352step0 raw1352step0Labels := by
      have ha : raw1352step0 = (fun i j => raw1352 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1352step0 raw1352; decide +kernel
      have hl : raw1352step0Labels = raw1352Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1352 raw1352Labels permutation32 permutation6
    mixedMoment B raw1352step0 raw1352step0Labels = mixedMoment B raw1352step1 raw1352step1Labels := by
      have ha : raw1352step1 = -raw1352step0 := by apply Matrix.ext; change ∀ i j, raw1352step1 i j = -(raw1352step0 i j); unfold raw1352step1 raw1352step0; decide +kernel
      have hl : raw1352step1Labels = raw1352step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1352step1 raw1352step1Labels = mixedMoment B raw1352step2 raw1352step2Labels := by
      have ha : raw1352step2 = raw1352step1 := by apply Matrix.ext; unfold raw1352step2 raw1352step1; decide +kernel
      have hl : raw1352step1Labels = labelEmbedding1 ∘ raw1352step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1352step1 raw1352step1Labels raw1352step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3252 node3252Labels := by rfl

def raw1353 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1353step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1353step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1353step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1353 raw1353Labels = mixedMoment B node4537 node4537Labels := by
  calc
    mixedMoment B raw1353 raw1353Labels = mixedMoment B raw1353step0 raw1353step0Labels := by
      have ha : raw1353step0 = (fun i j => raw1353 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1353step0 raw1353; decide +kernel
      have hl : raw1353step0Labels = raw1353Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1353 raw1353Labels permutation152 permutation4
    mixedMoment B raw1353step0 raw1353step0Labels = mixedMoment B raw1353step1 raw1353step1Labels := by
      have ha : raw1353step1 = raw1353step0 := by apply Matrix.ext; unfold raw1353step1 raw1353step0; decide +kernel
      have hl : raw1353step0Labels = labelEmbedding7 ∘ raw1353step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1353step0 raw1353step0Labels raw1353step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4537 node4537Labels := by rfl

def raw1354 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1354Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1354step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1354 raw1354Labels = mixedMoment B node1122 node1122Labels := by
  calc
    mixedMoment B raw1354 raw1354Labels = mixedMoment B raw1354step0 raw1354step0Labels := by
      have ha : raw1354step0 = (fun i j => raw1354 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1354step0 raw1354; decide +kernel
      have hl : raw1354step0Labels = raw1354Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1354 raw1354Labels permutation152 permutation4
    _ = mixedMoment B node1122 node1122Labels := by rfl

def raw1355 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1355Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1355step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1355step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1355step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1355step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1355step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1355step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1355 raw1355Labels = mixedMoment B node3253 node3253Labels := by
  calc
    mixedMoment B raw1355 raw1355Labels = mixedMoment B raw1355step0 raw1355step0Labels := by
      have ha : raw1355step0 = (fun i j => raw1355 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1355step0 raw1355; decide +kernel
      have hl : raw1355step0Labels = raw1355Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1355 raw1355Labels permutation152 permutation6
    mixedMoment B raw1355step0 raw1355step0Labels = mixedMoment B raw1355step1 raw1355step1Labels := by
      have ha : raw1355step1 = -raw1355step0 := by apply Matrix.ext; change ∀ i j, raw1355step1 i j = -(raw1355step0 i j); unfold raw1355step1 raw1355step0; decide +kernel
      have hl : raw1355step1Labels = raw1355step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1355step1 raw1355step1Labels = mixedMoment B raw1355step2 raw1355step2Labels := by
      have ha : raw1355step2 = raw1355step1 := by apply Matrix.ext; unfold raw1355step2 raw1355step1; decide +kernel
      have hl : raw1355step1Labels = labelEmbedding1 ∘ raw1355step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1355step1 raw1355step1Labels raw1355step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3253 node3253Labels := by rfl

def raw1356 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1356step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1356step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1356 raw1356Labels = mixedMoment B node4538 node4538Labels := by
  calc
    mixedMoment B raw1356 raw1356Labels = mixedMoment B raw1356step0 raw1356step0Labels := by
      have ha : raw1356step0 = (fun i j => raw1356 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1356step0 raw1356; decide +kernel
      have hl : raw1356step0Labels = raw1356Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1356 raw1356Labels permutation32 permutation4
    mixedMoment B raw1356step0 raw1356step0Labels = mixedMoment B raw1356step1 raw1356step1Labels := by
      have ha : raw1356step1 = raw1356step0 := by apply Matrix.ext; unfold raw1356step1 raw1356step0; decide +kernel
      have hl : raw1356step0Labels = labelEmbedding7 ∘ raw1356step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1356step0 raw1356step0Labels raw1356step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4538 node4538Labels := by rfl

def raw1357 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1357Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw1357step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1357 raw1357Labels = mixedMoment B node1123 node1123Labels := by
  calc
    mixedMoment B raw1357 raw1357Labels = mixedMoment B raw1357step0 raw1357step0Labels := by
      have ha : raw1357step0 = (fun i j => raw1357 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1357step0 raw1357; decide +kernel
      have hl : raw1357step0Labels = raw1357Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1357 raw1357Labels permutation32 permutation4
    _ = mixedMoment B node1123 node1123Labels := by rfl

def raw1358 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 3, -3]]
def raw1358Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 2, -4]]
def raw1358step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 2, -4]]
def raw1358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1358 raw1358Labels = mixedMoment B node1937 node1937Labels := by
  calc
    mixedMoment B raw1358 raw1358Labels = mixedMoment B raw1358step0 raw1358step0Labels := by
      have ha : raw1358step0 = (fun i j => raw1358 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1358step0 raw1358; decide +kernel
      have hl : raw1358step0Labels = raw1358Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1358 raw1358Labels permutation151 permutation6
    mixedMoment B raw1358step0 raw1358step0Labels = mixedMoment B raw1358step1 raw1358step1Labels := by
      have ha : raw1358step1 = raw1358step0 := by apply Matrix.ext; unfold raw1358step1 raw1358step0; decide +kernel
      have hl : raw1358step0Labels = labelEmbedding1 ∘ raw1358step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1358step0 raw1358step0Labels raw1358step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1937 node1937Labels := by rfl

def raw1359 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1359step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1359step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1359step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1359 raw1359Labels = mixedMoment B node4539 node4539Labels := by
  calc
    mixedMoment B raw1359 raw1359Labels = mixedMoment B raw1359step0 raw1359step0Labels := by
      have ha : raw1359step0 = (fun i j => raw1359 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1359step0 raw1359; decide +kernel
      have hl : raw1359step0Labels = raw1359Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1359 raw1359Labels permutation32 permutation4
    mixedMoment B raw1359step0 raw1359step0Labels = mixedMoment B raw1359step1 raw1359step1Labels := by
      have ha : raw1359step1 = raw1359step0 := by apply Matrix.ext; unfold raw1359step1 raw1359step0; decide +kernel
      have hl : raw1359step0Labels = labelEmbedding7 ∘ raw1359step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1359step0 raw1359step0Labels raw1359step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4539 node4539Labels := by rfl

def raw1360 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1360Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw1360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1360 raw1360Labels = mixedMoment B node1124 node1124Labels := by
  calc
    mixedMoment B raw1360 raw1360Labels = mixedMoment B raw1360step0 raw1360step0Labels := by
      have ha : raw1360step0 = (fun i j => raw1360 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1360step0 raw1360; decide +kernel
      have hl : raw1360step0Labels = raw1360Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1360 raw1360Labels permutation32 permutation4
    _ = mixedMoment B node1124 node1124Labels := by rfl

def raw1361 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 1, 1], ![0, 2, -2], ![0, 2, -2]]
def raw1361Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -2, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw1361step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1361step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1361step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw1361step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1361 raw1361Labels = mixedMoment B node3254 node3254Labels := by
  calc
    mixedMoment B raw1361 raw1361Labels = mixedMoment B raw1361step0 raw1361step0Labels := by
      have ha : raw1361step0 = (fun i j => raw1361 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1361step0 raw1361; decide +kernel
      have hl : raw1361step0Labels = raw1361Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1361 raw1361Labels permutation32 permutation6
    mixedMoment B raw1361step0 raw1361step0Labels = mixedMoment B raw1361step1 raw1361step1Labels := by
      have ha : raw1361step1 = -raw1361step0 := by apply Matrix.ext; change ∀ i j, raw1361step1 i j = -(raw1361step0 i j); unfold raw1361step1 raw1361step0; decide +kernel
      have hl : raw1361step1Labels = raw1361step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1361step1 raw1361step1Labels = mixedMoment B raw1361step2 raw1361step2Labels := by
      have ha : raw1361step2 = raw1361step1 := by apply Matrix.ext; unfold raw1361step2 raw1361step1; decide +kernel
      have hl : raw1361step1Labels = labelEmbedding1 ∘ raw1361step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1361step1 raw1361step1Labels raw1361step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3254 node3254Labels := by rfl

def raw1362 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1362step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1362step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1362step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1362 raw1362Labels = mixedMoment B node4541 node4541Labels := by
  calc
    mixedMoment B raw1362 raw1362Labels = mixedMoment B raw1362step0 raw1362step0Labels := by
      have ha : raw1362step0 = (fun i j => raw1362 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1362step0 raw1362; decide +kernel
      have hl : raw1362step0Labels = raw1362Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1362 raw1362Labels permutation152 permutation4
    mixedMoment B raw1362step0 raw1362step0Labels = mixedMoment B raw1362step1 raw1362step1Labels := by
      have ha : raw1362step1 = raw1362step0 := by apply Matrix.ext; unfold raw1362step1 raw1362step0; decide +kernel
      have hl : raw1362step0Labels = labelEmbedding7 ∘ raw1362step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1362step0 raw1362step0Labels raw1362step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4541 node4541Labels := by rfl

def raw1363 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1363Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw1363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1363 raw1363Labels = mixedMoment B node1126 node1126Labels := by
  calc
    mixedMoment B raw1363 raw1363Labels = mixedMoment B raw1363step0 raw1363step0Labels := by
      have ha : raw1363step0 = (fun i j => raw1363 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1363step0 raw1363; decide +kernel
      have hl : raw1363step0Labels = raw1363Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1363 raw1363Labels permutation152 permutation4
    _ = mixedMoment B node1126 node1126Labels := by rfl

def raw1364 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2]]
def raw1364Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1364step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1364step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1364step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1364step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1364step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1364step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1364 raw1364Labels = mixedMoment B node3256 node3256Labels := by
  calc
    mixedMoment B raw1364 raw1364Labels = mixedMoment B raw1364step0 raw1364step0Labels := by
      have ha : raw1364step0 = (fun i j => raw1364 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1364step0 raw1364; decide +kernel
      have hl : raw1364step0Labels = raw1364Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1364 raw1364Labels permutation152 permutation6
    mixedMoment B raw1364step0 raw1364step0Labels = mixedMoment B raw1364step1 raw1364step1Labels := by
      have ha : raw1364step1 = -raw1364step0 := by apply Matrix.ext; change ∀ i j, raw1364step1 i j = -(raw1364step0 i j); unfold raw1364step1 raw1364step0; decide +kernel
      have hl : raw1364step1Labels = raw1364step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1364step1 raw1364step1Labels = mixedMoment B raw1364step2 raw1364step2Labels := by
      have ha : raw1364step2 = raw1364step1 := by apply Matrix.ext; unfold raw1364step2 raw1364step1; decide +kernel
      have hl : raw1364step1Labels = labelEmbedding1 ∘ raw1364step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1364step1 raw1364step1Labels raw1364step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3256 node3256Labels := by rfl

def raw1365 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1365step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1365step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1365 raw1365Labels = mixedMoment B node4543 node4543Labels := by
  calc
    mixedMoment B raw1365 raw1365Labels = mixedMoment B raw1365step0 raw1365step0Labels := by
      have ha : raw1365step0 = (fun i j => raw1365 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1365step0 raw1365; decide +kernel
      have hl : raw1365step0Labels = raw1365Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1365 raw1365Labels permutation32 permutation4
    mixedMoment B raw1365step0 raw1365step0Labels = mixedMoment B raw1365step1 raw1365step1Labels := by
      have ha : raw1365step1 = raw1365step0 := by apply Matrix.ext; unfold raw1365step1 raw1365step0; decide +kernel
      have hl : raw1365step0Labels = labelEmbedding7 ∘ raw1365step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1365step0 raw1365step0Labels raw1365step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4543 node4543Labels := by rfl

def raw1366 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw1366step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1366 raw1366Labels = mixedMoment B node1128 node1128Labels := by
  calc
    mixedMoment B raw1366 raw1366Labels = mixedMoment B raw1366step0 raw1366step0Labels := by
      have ha : raw1366step0 = (fun i j => raw1366 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1366step0 raw1366; decide +kernel
      have hl : raw1366step0Labels = raw1366Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1366 raw1366Labels permutation32 permutation4
    _ = mixedMoment B node1128 node1128Labels := by rfl

def raw1367 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![0, 3, -3]]
def raw1367Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw1367step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw1367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1367 raw1367Labels = mixedMoment B node2184 node2184Labels := by
  calc
    mixedMoment B raw1367 raw1367Labels = mixedMoment B raw1367step0 raw1367step0Labels := by
      have ha : raw1367step0 = (fun i j => raw1367 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1367step0 raw1367; decide +kernel
      have hl : raw1367step0Labels = raw1367Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1367 raw1367Labels permutation145 permutation6
    mixedMoment B raw1367step0 raw1367step0Labels = mixedMoment B raw1367step1 raw1367step1Labels := by
      have ha : raw1367step1 = raw1367step0 := by apply Matrix.ext; unfold raw1367step1 raw1367step0; decide +kernel
      have hl : raw1367step0Labels = labelEmbedding1 ∘ raw1367step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1367step0 raw1367step0Labels raw1367step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2184 node2184Labels := by rfl

def raw1368 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1368Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1368step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1368step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1368step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1368 raw1368Labels = mixedMoment B node4544 node4544Labels := by
  calc
    mixedMoment B raw1368 raw1368Labels = mixedMoment B raw1368step0 raw1368step0Labels := by
      have ha : raw1368step0 = (fun i j => raw1368 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1368step0 raw1368; decide +kernel
      have hl : raw1368step0Labels = raw1368Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1368 raw1368Labels permutation152 permutation4
    mixedMoment B raw1368step0 raw1368step0Labels = mixedMoment B raw1368step1 raw1368step1Labels := by
      have ha : raw1368step1 = raw1368step0 := by apply Matrix.ext; unfold raw1368step1 raw1368step0; decide +kernel
      have hl : raw1368step0Labels = labelEmbedding7 ∘ raw1368step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1368step0 raw1368step0Labels raw1368step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4544 node4544Labels := by rfl

def raw1369 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw1369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1369 raw1369Labels = mixedMoment B node1129 node1129Labels := by
  calc
    mixedMoment B raw1369 raw1369Labels = mixedMoment B raw1369step0 raw1369step0Labels := by
      have ha : raw1369step0 = (fun i j => raw1369 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1369step0 raw1369; decide +kernel
      have hl : raw1369step0Labels = raw1369Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1369 raw1369Labels permutation152 permutation4
    _ = mixedMoment B node1129 node1129Labels := by rfl

def raw1370 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1]]
def raw1370Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw1370step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1370step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1370step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw1370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1370 raw1370Labels = mixedMoment B node3263 node3263Labels := by
  calc
    mixedMoment B raw1370 raw1370Labels = mixedMoment B raw1370step0 raw1370step0Labels := by
      have ha : raw1370step0 = (fun i j => raw1370 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1370step0 raw1370; decide +kernel
      have hl : raw1370step0Labels = raw1370Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1370 raw1370Labels permutation152 permutation6
    mixedMoment B raw1370step0 raw1370step0Labels = mixedMoment B raw1370step1 raw1370step1Labels := by
      have ha : raw1370step1 = -raw1370step0 := by apply Matrix.ext; change ∀ i j, raw1370step1 i j = -(raw1370step0 i j); unfold raw1370step1 raw1370step0; decide +kernel
      have hl : raw1370step1Labels = raw1370step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1370step1 raw1370step1Labels = mixedMoment B raw1370step2 raw1370step2Labels := by
      have ha : raw1370step2 = raw1370step1 := by apply Matrix.ext; unfold raw1370step2 raw1370step1; decide +kernel
      have hl : raw1370step1Labels = labelEmbedding1 ∘ raw1370step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1370step1 raw1370step1Labels raw1370step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3263 node3263Labels := by rfl

def raw1371 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1371Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1371step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1371step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1371 raw1371Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw1371 raw1371Labels = mixedMoment B raw1371step0 raw1371step0Labels := by
      have ha : raw1371step0 = (fun i j => raw1371 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1371step0 raw1371; decide +kernel
      have hl : raw1371step0Labels = raw1371Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1371 raw1371Labels permutation32 permutation4
    mixedMoment B raw1371step0 raw1371step0Labels = mixedMoment B raw1371step1 raw1371step1Labels := by
      have ha : raw1371step1 = raw1371step0 := by apply Matrix.ext; unfold raw1371step1 raw1371step0; decide +kernel
      have hl : raw1371step0Labels = labelEmbedding7 ∘ raw1371step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1371step0 raw1371step0Labels raw1371step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4546 node4546Labels := by rfl

def raw1372 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw1372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1372 raw1372Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw1372 raw1372Labels = mixedMoment B raw1372step0 raw1372step0Labels := by
      have ha : raw1372step0 = (fun i j => raw1372 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1372step0 raw1372; decide +kernel
      have hl : raw1372step0Labels = raw1372Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1372 raw1372Labels permutation32 permutation4
    _ = mixedMoment B node1131 node1131Labels := by rfl

def raw1373 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![-1, 3, -2]]
def raw1373Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, -1, 3]]
def raw1373step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1373step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1373step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw1373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1373 raw1373Labels = mixedMoment B node3264 node3264Labels := by
  calc
    mixedMoment B raw1373 raw1373Labels = mixedMoment B raw1373step0 raw1373step0Labels := by
      have ha : raw1373step0 = (fun i j => raw1373 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1373step0 raw1373; decide +kernel
      have hl : raw1373step0Labels = raw1373Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1373 raw1373Labels permutation32 permutation6
    mixedMoment B raw1373step0 raw1373step0Labels = mixedMoment B raw1373step1 raw1373step1Labels := by
      have ha : raw1373step1 = -raw1373step0 := by apply Matrix.ext; change ∀ i j, raw1373step1 i j = -(raw1373step0 i j); unfold raw1373step1 raw1373step0; decide +kernel
      have hl : raw1373step1Labels = raw1373step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1373step1 raw1373step1Labels = mixedMoment B raw1373step2 raw1373step2Labels := by
      have ha : raw1373step2 = raw1373step1 := by apply Matrix.ext; unfold raw1373step2 raw1373step1; decide +kernel
      have hl : raw1373step1Labels = labelEmbedding1 ∘ raw1373step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1373step1 raw1373step1Labels raw1373step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3264 node3264Labels := by rfl

def raw1374 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1374step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1374step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1374 raw1374Labels = mixedMoment B node4549 node4549Labels := by
  calc
    mixedMoment B raw1374 raw1374Labels = mixedMoment B raw1374step0 raw1374step0Labels := by
      have ha : raw1374step0 = (fun i j => raw1374 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1374step0 raw1374; decide +kernel
      have hl : raw1374step0Labels = raw1374Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1374 raw1374Labels permutation32 permutation4
    mixedMoment B raw1374step0 raw1374step0Labels = mixedMoment B raw1374step1 raw1374step1Labels := by
      have ha : raw1374step1 = raw1374step0 := by apply Matrix.ext; unfold raw1374step1 raw1374step0; decide +kernel
      have hl : raw1374step0Labels = labelEmbedding7 ∘ raw1374step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1374step0 raw1374step0Labels raw1374step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4549 node4549Labels := by rfl

def raw1375 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw1375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1375 raw1375Labels = mixedMoment B node1134 node1134Labels := by
  calc
    mixedMoment B raw1375 raw1375Labels = mixedMoment B raw1375step0 raw1375step0Labels := by
      have ha : raw1375step0 = (fun i j => raw1375 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1375step0 raw1375; decide +kernel
      have hl : raw1375step0Labels = raw1375Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1375 raw1375Labels permutation32 permutation4
    _ = mixedMoment B node1134 node1134Labels := by rfl

def raw1376 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 1, 0], ![-1, 2, -1], ![0, 2, -2]]
def raw1376Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw1376step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1376step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1376step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw1376step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1376 raw1376Labels = mixedMoment B node3265 node3265Labels := by
  calc
    mixedMoment B raw1376 raw1376Labels = mixedMoment B raw1376step0 raw1376step0Labels := by
      have ha : raw1376step0 = (fun i j => raw1376 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1376step0 raw1376; decide +kernel
      have hl : raw1376step0Labels = raw1376Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1376 raw1376Labels permutation32 permutation6
    mixedMoment B raw1376step0 raw1376step0Labels = mixedMoment B raw1376step1 raw1376step1Labels := by
      have ha : raw1376step1 = -raw1376step0 := by apply Matrix.ext; change ∀ i j, raw1376step1 i j = -(raw1376step0 i j); unfold raw1376step1 raw1376step0; decide +kernel
      have hl : raw1376step1Labels = raw1376step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1376step1 raw1376step1Labels = mixedMoment B raw1376step2 raw1376step2Labels := by
      have ha : raw1376step2 = raw1376step1 := by apply Matrix.ext; unfold raw1376step2 raw1376step1; decide +kernel
      have hl : raw1376step1Labels = labelEmbedding1 ∘ raw1376step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1376step1 raw1376step1Labels raw1376step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3265 node3265Labels := by rfl

def raw1377 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1377step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1377step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1377 raw1377Labels = mixedMoment B node4550 node4550Labels := by
  calc
    mixedMoment B raw1377 raw1377Labels = mixedMoment B raw1377step0 raw1377step0Labels := by
      have ha : raw1377step0 = (fun i j => raw1377 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1377step0 raw1377; decide +kernel
      have hl : raw1377step0Labels = raw1377Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1377 raw1377Labels permutation152 permutation4
    mixedMoment B raw1377step0 raw1377step0Labels = mixedMoment B raw1377step1 raw1377step1Labels := by
      have ha : raw1377step1 = raw1377step0 := by apply Matrix.ext; unfold raw1377step1 raw1377step0; decide +kernel
      have hl : raw1377step0Labels = labelEmbedding7 ∘ raw1377step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1377step0 raw1377step0Labels raw1377step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4550 node4550Labels := by rfl

def raw1378 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw1378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1378 raw1378Labels = mixedMoment B node1135 node1135Labels := by
  calc
    mixedMoment B raw1378 raw1378Labels = mixedMoment B raw1378step0 raw1378step0Labels := by
      have ha : raw1378step0 = (fun i j => raw1378 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1378step0 raw1378; decide +kernel
      have hl : raw1378step0Labels = raw1378Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1378 raw1378Labels permutation152 permutation4
    _ = mixedMoment B node1135 node1135Labels := by rfl

def raw1379 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-2, 2, 0]]
def raw1379Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1379step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1379step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1379step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1379step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1379 raw1379Labels = mixedMoment B node3269 node3269Labels := by
  calc
    mixedMoment B raw1379 raw1379Labels = mixedMoment B raw1379step0 raw1379step0Labels := by
      have ha : raw1379step0 = (fun i j => raw1379 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1379step0 raw1379; decide +kernel
      have hl : raw1379step0Labels = raw1379Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1379 raw1379Labels permutation170 permutation6
    mixedMoment B raw1379step0 raw1379step0Labels = mixedMoment B raw1379step1 raw1379step1Labels := by
      have ha : raw1379step1 = -raw1379step0 := by apply Matrix.ext; change ∀ i j, raw1379step1 i j = -(raw1379step0 i j); unfold raw1379step1 raw1379step0; decide +kernel
      have hl : raw1379step1Labels = raw1379step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1379step1 raw1379step1Labels = mixedMoment B raw1379step2 raw1379step2Labels := by
      have ha : raw1379step2 = raw1379step1 := by apply Matrix.ext; unfold raw1379step2 raw1379step1; decide +kernel
      have hl : raw1379step1Labels = labelEmbedding1 ∘ raw1379step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1379step1 raw1379step1Labels raw1379step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3269 node3269Labels := by rfl

def raw1380 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1380step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1380step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1380 raw1380Labels = mixedMoment B node4551 node4551Labels := by
  calc
    mixedMoment B raw1380 raw1380Labels = mixedMoment B raw1380step0 raw1380step0Labels := by
      have ha : raw1380step0 = (fun i j => raw1380 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1380step0 raw1380; decide +kernel
      have hl : raw1380step0Labels = raw1380Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1380 raw1380Labels permutation32 permutation4
    mixedMoment B raw1380step0 raw1380step0Labels = mixedMoment B raw1380step1 raw1380step1Labels := by
      have ha : raw1380step1 = raw1380step0 := by apply Matrix.ext; unfold raw1380step1 raw1380step0; decide +kernel
      have hl : raw1380step0Labels = labelEmbedding7 ∘ raw1380step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1380step0 raw1380step0Labels raw1380step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4551 node4551Labels := by rfl

def raw1381 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw1381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1381 raw1381Labels = mixedMoment B node1136 node1136Labels := by
  calc
    mixedMoment B raw1381 raw1381Labels = mixedMoment B raw1381step0 raw1381step0Labels := by
      have ha : raw1381step0 = (fun i j => raw1381 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1381step0 raw1381; decide +kernel
      have hl : raw1381step0Labels = raw1381Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1381 raw1381Labels permutation32 permutation4
    _ = mixedMoment B node1136 node1136Labels := by rfl

def raw1382 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![-2, 3, -1]]
def raw1382Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw1382step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1382step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1382step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw1382step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1382 raw1382Labels = mixedMoment B node3273 node3273Labels := by
  calc
    mixedMoment B raw1382 raw1382Labels = mixedMoment B raw1382step0 raw1382step0Labels := by
      have ha : raw1382step0 = (fun i j => raw1382 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1382step0 raw1382; decide +kernel
      have hl : raw1382step0Labels = raw1382Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1382 raw1382Labels permutation32 permutation6
    mixedMoment B raw1382step0 raw1382step0Labels = mixedMoment B raw1382step1 raw1382step1Labels := by
      have ha : raw1382step1 = -raw1382step0 := by apply Matrix.ext; change ∀ i j, raw1382step1 i j = -(raw1382step0 i j); unfold raw1382step1 raw1382step0; decide +kernel
      have hl : raw1382step1Labels = raw1382step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1382step1 raw1382step1Labels = mixedMoment B raw1382step2 raw1382step2Labels := by
      have ha : raw1382step2 = raw1382step1 := by apply Matrix.ext; unfold raw1382step2 raw1382step1; decide +kernel
      have hl : raw1382step1Labels = labelEmbedding1 ∘ raw1382step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1382step1 raw1382step1Labels raw1382step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3273 node3273Labels := by rfl

def raw1383 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1383step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1383step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1383 raw1383Labels = mixedMoment B node4553 node4553Labels := by
  calc
    mixedMoment B raw1383 raw1383Labels = mixedMoment B raw1383step0 raw1383step0Labels := by
      have ha : raw1383step0 = (fun i j => raw1383 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1383step0 raw1383; decide +kernel
      have hl : raw1383step0Labels = raw1383Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1383 raw1383Labels permutation32 permutation4
    mixedMoment B raw1383step0 raw1383step0Labels = mixedMoment B raw1383step1 raw1383step1Labels := by
      have ha : raw1383step1 = raw1383step0 := by apply Matrix.ext; unfold raw1383step1 raw1383step0; decide +kernel
      have hl : raw1383step0Labels = labelEmbedding7 ∘ raw1383step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1383step0 raw1383step0Labels raw1383step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4553 node4553Labels := by rfl

def raw1384 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1384Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw1384step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1384 raw1384Labels = mixedMoment B node1138 node1138Labels := by
  calc
    mixedMoment B raw1384 raw1384Labels = mixedMoment B raw1384step0 raw1384step0Labels := by
      have ha : raw1384step0 = (fun i j => raw1384 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1384step0 raw1384; decide +kernel
      have hl : raw1384step0Labels = raw1384Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1384 raw1384Labels permutation32 permutation4
    _ = mixedMoment B node1138 node1138Labels := by rfl

def raw1385 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-2, 2, 0], ![0, 2, -2]]
def raw1385Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw1385step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1385step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw1385step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1385 raw1385Labels = mixedMoment B node3270 node3270Labels := by
  calc
    mixedMoment B raw1385 raw1385Labels = mixedMoment B raw1385step0 raw1385step0Labels := by
      have ha : raw1385step0 = (fun i j => raw1385 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1385step0 raw1385; decide +kernel
      have hl : raw1385step0Labels = raw1385Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1385 raw1385Labels permutation34 permutation6
    mixedMoment B raw1385step0 raw1385step0Labels = mixedMoment B raw1385step1 raw1385step1Labels := by
      have ha : raw1385step1 = -raw1385step0 := by apply Matrix.ext; change ∀ i j, raw1385step1 i j = -(raw1385step0 i j); unfold raw1385step1 raw1385step0; decide +kernel
      have hl : raw1385step1Labels = raw1385step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1385step1 raw1385step1Labels = mixedMoment B raw1385step2 raw1385step2Labels := by
      have ha : raw1385step2 = raw1385step1 := by apply Matrix.ext; unfold raw1385step2 raw1385step1; decide +kernel
      have hl : raw1385step1Labels = labelEmbedding1 ∘ raw1385step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1385step1 raw1385step1Labels raw1385step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3270 node3270Labels := by rfl

def raw1386 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1386step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1386step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1386 raw1386Labels = mixedMoment B node4554 node4554Labels := by
  calc
    mixedMoment B raw1386 raw1386Labels = mixedMoment B raw1386step0 raw1386step0Labels := by
      have ha : raw1386step0 = (fun i j => raw1386 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1386step0 raw1386; decide +kernel
      have hl : raw1386step0Labels = raw1386Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1386 raw1386Labels permutation32 permutation4
    mixedMoment B raw1386step0 raw1386step0Labels = mixedMoment B raw1386step1 raw1386step1Labels := by
      have ha : raw1386step1 = raw1386step0 := by apply Matrix.ext; unfold raw1386step1 raw1386step0; decide +kernel
      have hl : raw1386step0Labels = labelEmbedding7 ∘ raw1386step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1386step0 raw1386step0Labels raw1386step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4554 node4554Labels := by rfl

def raw1387 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1387Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw1387step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1387 raw1387Labels = mixedMoment B node1139 node1139Labels := by
  calc
    mixedMoment B raw1387 raw1387Labels = mixedMoment B raw1387step0 raw1387step0Labels := by
      have ha : raw1387step0 = (fun i j => raw1387 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1387step0 raw1387; decide +kernel
      have hl : raw1387step0Labels = raw1387Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1387 raw1387Labels permutation32 permutation4
    _ = mixedMoment B node1139 node1139Labels := by rfl

def raw1388 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 2, -1]]
def raw1388Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw1388step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1388step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1388step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw1388step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1388 raw1388Labels = mixedMoment B node3274 node3274Labels := by
  calc
    mixedMoment B raw1388 raw1388Labels = mixedMoment B raw1388step0 raw1388step0Labels := by
      have ha : raw1388step0 = (fun i j => raw1388 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1388step0 raw1388; decide +kernel
      have hl : raw1388step0Labels = raw1388Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1388 raw1388Labels permutation32 permutation6
    mixedMoment B raw1388step0 raw1388step0Labels = mixedMoment B raw1388step1 raw1388step1Labels := by
      have ha : raw1388step1 = -raw1388step0 := by apply Matrix.ext; change ∀ i j, raw1388step1 i j = -(raw1388step0 i j); unfold raw1388step1 raw1388step0; decide +kernel
      have hl : raw1388step1Labels = raw1388step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1388step1 raw1388step1Labels = mixedMoment B raw1388step2 raw1388step2Labels := by
      have ha : raw1388step2 = raw1388step1 := by apply Matrix.ext; unfold raw1388step2 raw1388step1; decide +kernel
      have hl : raw1388step1Labels = labelEmbedding1 ∘ raw1388step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1388step1 raw1388step1Labels raw1388step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3274 node3274Labels := by rfl

def raw1389 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-2, 4, -2]]
def raw1389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1389step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw1389step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1389step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw1389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1389 raw1389Labels = mixedMoment B node4555 node4555Labels := by
  calc
    mixedMoment B raw1389 raw1389Labels = mixedMoment B raw1389step0 raw1389step0Labels := by
      have ha : raw1389step0 = (fun i j => raw1389 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1389step0 raw1389; decide +kernel
      have hl : raw1389step0Labels = raw1389Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1389 raw1389Labels permutation8 permutation4
    mixedMoment B raw1389step0 raw1389step0Labels = mixedMoment B raw1389step1 raw1389step1Labels := by
      have ha : raw1389step1 = raw1389step0 := by apply Matrix.ext; unfold raw1389step1 raw1389step0; decide +kernel
      have hl : raw1389step0Labels = labelEmbedding7 ∘ raw1389step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1389step0 raw1389step0Labels raw1389step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4555 node4555Labels := by rfl

def raw1390 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-2, 4, -2]]
def raw1390Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1390step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![4, -2, -2]]
def raw1390step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1390 raw1390Labels = mixedMoment B node1140 node1140Labels := by
  calc
    mixedMoment B raw1390 raw1390Labels = mixedMoment B raw1390step0 raw1390step0Labels := by
      have ha : raw1390step0 = (fun i j => raw1390 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1390step0 raw1390; decide +kernel
      have hl : raw1390step0Labels = raw1390Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1390 raw1390Labels permutation8 permutation4
    _ = mixedMoment B node1140 node1140Labels := by rfl

def raw1391 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 1, -1], ![-2, 4, -2]]
def raw1391Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1391step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![2, 2, -4]]
def raw1391step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1391step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![2, 2, -4]]
def raw1391step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1391 raw1391Labels = mixedMoment B node3275 node3275Labels := by
  calc
    mixedMoment B raw1391 raw1391Labels = mixedMoment B raw1391step0 raw1391step0Labels := by
      have ha : raw1391step0 = (fun i j => raw1391 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1391step0 raw1391; decide +kernel
      have hl : raw1391step0Labels = raw1391Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1391 raw1391Labels permutation31 permutation6
    mixedMoment B raw1391step0 raw1391step0Labels = mixedMoment B raw1391step1 raw1391step1Labels := by
      have ha : raw1391step1 = raw1391step0 := by apply Matrix.ext; unfold raw1391step1 raw1391step0; decide +kernel
      have hl : raw1391step0Labels = labelEmbedding1 ∘ raw1391step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1391step0 raw1391step0Labels raw1391step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3275 node3275Labels := by rfl

def raw1392 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw1392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1392step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw1392step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw1392step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1392 raw1392Labels = mixedMoment B node4557 node4557Labels := by
  calc
    mixedMoment B raw1392 raw1392Labels = mixedMoment B raw1392step0 raw1392step0Labels := by
      have ha : raw1392step0 = (fun i j => raw1392 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1392step0 raw1392; decide +kernel
      have hl : raw1392step0Labels = raw1392Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1392 raw1392Labels permutation8 permutation4
    mixedMoment B raw1392step0 raw1392step0Labels = mixedMoment B raw1392step1 raw1392step1Labels := by
      have ha : raw1392step1 = raw1392step0 := by apply Matrix.ext; unfold raw1392step1 raw1392step0; decide +kernel
      have hl : raw1392step0Labels = labelEmbedding7 ∘ raw1392step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1392step0 raw1392step0Labels raw1392step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4557 node4557Labels := by rfl

def raw1393 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw1393Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1393step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![3, 0, -3]]
def raw1393step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1393 raw1393Labels = mixedMoment B node1143 node1143Labels := by
  calc
    mixedMoment B raw1393 raw1393Labels = mixedMoment B raw1393step0 raw1393step0Labels := by
      have ha : raw1393step0 = (fun i j => raw1393 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1393step0 raw1393; decide +kernel
      have hl : raw1393step0Labels = raw1393Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1393 raw1393Labels permutation8 permutation4
    _ = mixedMoment B node1143 node1143Labels := by rfl

def raw1394 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-2, 2, 0], ![0, 3, -3]]
def raw1394Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1394step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw1394step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1394step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![1, 0, -1], ![2, 2, -4]]
def raw1394step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1394 raw1394Labels = mixedMoment B node2167 node2167Labels := by
  calc
    mixedMoment B raw1394 raw1394Labels = mixedMoment B raw1394step0 raw1394step0Labels := by
      have ha : raw1394step0 = (fun i j => raw1394 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1394step0 raw1394; decide +kernel
      have hl : raw1394step0Labels = raw1394Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1394 raw1394Labels permutation31 permutation6
    mixedMoment B raw1394step0 raw1394step0Labels = mixedMoment B raw1394step1 raw1394step1Labels := by
      have ha : raw1394step1 = raw1394step0 := by apply Matrix.ext; unfold raw1394step1 raw1394step0; decide +kernel
      have hl : raw1394step0Labels = labelEmbedding1 ∘ raw1394step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1394step0 raw1394step0Labels raw1394step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2167 node2167Labels := by rfl

def raw1395 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1395step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw1395step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1395step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw1395step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1395 raw1395Labels = mixedMoment B node4558 node4558Labels := by
  calc
    mixedMoment B raw1395 raw1395Labels = mixedMoment B raw1395step0 raw1395step0Labels := by
      have ha : raw1395step0 = (fun i j => raw1395 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1395step0 raw1395; decide +kernel
      have hl : raw1395step0Labels = raw1395Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1395 raw1395Labels permutation8 permutation4
    mixedMoment B raw1395step0 raw1395step0Labels = mixedMoment B raw1395step1 raw1395step1Labels := by
      have ha : raw1395step1 = raw1395step0 := by apply Matrix.ext; unfold raw1395step1 raw1395step0; decide +kernel
      have hl : raw1395step0Labels = labelEmbedding7 ∘ raw1395step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1395step0 raw1395step0Labels raw1395step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4558 node4558Labels := by rfl

def raw1396 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1396Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1396step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw1396step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1396 raw1396Labels = mixedMoment B node1144 node1144Labels := by
  calc
    mixedMoment B raw1396 raw1396Labels = mixedMoment B raw1396step0 raw1396step0Labels := by
      have ha : raw1396step0 = (fun i j => raw1396 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1396step0 raw1396; decide +kernel
      have hl : raw1396step0Labels = raw1396Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1396 raw1396Labels permutation8 permutation4
    _ = mixedMoment B node1144 node1144Labels := by rfl

def raw1397 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![-1, 2, -1], ![-1, 3, -2]]
def raw1397Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1397step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw1397step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw1397step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw1397step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1397 raw1397Labels = mixedMoment B node3276 node3276Labels := by
  calc
    mixedMoment B raw1397 raw1397Labels = mixedMoment B raw1397step0 raw1397step0Labels := by
      have ha : raw1397step0 = (fun i j => raw1397 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1397step0 raw1397; decide +kernel
      have hl : raw1397step0Labels = raw1397Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1397 raw1397Labels permutation8 permutation6
    mixedMoment B raw1397step0 raw1397step0Labels = mixedMoment B raw1397step1 raw1397step1Labels := by
      have ha : raw1397step1 = -raw1397step0 := by apply Matrix.ext; change ∀ i j, raw1397step1 i j = -(raw1397step0 i j); unfold raw1397step1 raw1397step0; decide +kernel
      have hl : raw1397step1Labels = raw1397step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1397step1 raw1397step1Labels = mixedMoment B raw1397step2 raw1397step2Labels := by
      have ha : raw1397step2 = raw1397step1 := by apply Matrix.ext; unfold raw1397step2 raw1397step1; decide +kernel
      have hl : raw1397step1Labels = labelEmbedding1 ∘ raw1397step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1397step1 raw1397step1Labels raw1397step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3276 node3276Labels := by rfl

def raw1398 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 2, -2], ![-2, 3, -1]]
def raw1398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1398step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw1398step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw1398step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1398 raw1398Labels = mixedMoment B node4559 node4559Labels := by
  calc
    mixedMoment B raw1398 raw1398Labels = mixedMoment B raw1398step0 raw1398step0Labels := by
      have ha : raw1398step0 = (fun i j => raw1398 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1398step0 raw1398; decide +kernel
      have hl : raw1398step0Labels = raw1398Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1398 raw1398Labels permutation8 permutation4
    mixedMoment B raw1398step0 raw1398step0Labels = mixedMoment B raw1398step1 raw1398step1Labels := by
      have ha : raw1398step1 = raw1398step0 := by apply Matrix.ext; unfold raw1398step1 raw1398step0; decide +kernel
      have hl : raw1398step0Labels = labelEmbedding7 ∘ raw1398step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1398step0 raw1398step0Labels raw1398step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4559 node4559Labels := by rfl

def raw1399 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 2, -2], ![-2, 3, -1]]
def raw1399Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1399step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw1399step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1399 raw1399Labels = mixedMoment B node1145 node1145Labels := by
  calc
    mixedMoment B raw1399 raw1399Labels = mixedMoment B raw1399step0 raw1399step0Labels := by
      have ha : raw1399step0 = (fun i j => raw1399 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1399step0 raw1399; decide +kernel
      have hl : raw1399step0Labels = raw1399Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1399 raw1399Labels permutation8 permutation4
    _ = mixedMoment B node1145 node1145Labels := by rfl

def raw1400 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![0, -1, 1], ![0, 2, -2], ![-2, 3, -1]]
def raw1400Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1400step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw1400step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1400step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw1400step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1400step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw1400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1400 raw1400Labels = mixedMoment B node3277 node3277Labels := by
  calc
    mixedMoment B raw1400 raw1400Labels = mixedMoment B raw1400step0 raw1400step0Labels := by
      have ha : raw1400step0 = (fun i j => raw1400 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1400step0 raw1400; decide +kernel
      have hl : raw1400step0Labels = raw1400Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1400 raw1400Labels permutation9 permutation6
    mixedMoment B raw1400step0 raw1400step0Labels = mixedMoment B raw1400step1 raw1400step1Labels := by
      have ha : raw1400step1 = -raw1400step0 := by apply Matrix.ext; change ∀ i j, raw1400step1 i j = -(raw1400step0 i j); unfold raw1400step1 raw1400step0; decide +kernel
      have hl : raw1400step1Labels = raw1400step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1400step1 raw1400step1Labels = mixedMoment B raw1400step2 raw1400step2Labels := by
      have ha : raw1400step2 = raw1400step1 := by apply Matrix.ext; unfold raw1400step2 raw1400step1; decide +kernel
      have hl : raw1400step1Labels = labelEmbedding1 ∘ raw1400step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1400step1 raw1400step1Labels raw1400step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3277 node3277Labels := by rfl

def raw1401 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1401step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1401step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1401step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1401 raw1401Labels = mixedMoment B node4569 node4569Labels := by
  calc
    mixedMoment B raw1401 raw1401Labels = mixedMoment B raw1401step0 raw1401step0Labels := by
      have ha : raw1401step0 = (fun i j => raw1401 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1401step0 raw1401; decide +kernel
      have hl : raw1401step0Labels = raw1401Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1401 raw1401Labels permutation152 permutation4
    mixedMoment B raw1401step0 raw1401step0Labels = mixedMoment B raw1401step1 raw1401step1Labels := by
      have ha : raw1401step1 = raw1401step0 := by apply Matrix.ext; unfold raw1401step1 raw1401step0; decide +kernel
      have hl : raw1401step0Labels = labelEmbedding7 ∘ raw1401step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1401step0 raw1401step0Labels raw1401step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4569 node4569Labels := by rfl

def raw1402 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1402Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1402step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1402 raw1402Labels = mixedMoment B node1187 node1187Labels := by
  calc
    mixedMoment B raw1402 raw1402Labels = mixedMoment B raw1402step0 raw1402step0Labels := by
      have ha : raw1402step0 = (fun i j => raw1402 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1402step0 raw1402; decide +kernel
      have hl : raw1402step0Labels = raw1402Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1402 raw1402Labels permutation152 permutation4
    _ = mixedMoment B node1187 node1187Labels := by rfl

def raw1403 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1]]
def raw1403Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw1403step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1403step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1403step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1403step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw1403step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1403 raw1403Labels = mixedMoment B node3244 node3244Labels := by
  calc
    mixedMoment B raw1403 raw1403Labels = mixedMoment B raw1403step0 raw1403step0Labels := by
      have ha : raw1403step0 = (fun i j => raw1403 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1403step0 raw1403; decide +kernel
      have hl : raw1403step0Labels = raw1403Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1403 raw1403Labels permutation152 permutation6
    mixedMoment B raw1403step0 raw1403step0Labels = mixedMoment B raw1403step1 raw1403step1Labels := by
      have ha : raw1403step1 = -raw1403step0 := by apply Matrix.ext; change ∀ i j, raw1403step1 i j = -(raw1403step0 i j); unfold raw1403step1 raw1403step0; decide +kernel
      have hl : raw1403step1Labels = raw1403step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1403step1 raw1403step1Labels = mixedMoment B raw1403step2 raw1403step2Labels := by
      have ha : raw1403step2 = raw1403step1 := by apply Matrix.ext; unfold raw1403step2 raw1403step1; decide +kernel
      have hl : raw1403step1Labels = labelEmbedding1 ∘ raw1403step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1403step1 raw1403step1Labels raw1403step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3244 node3244Labels := by rfl

def raw1404 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1404step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1404step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1404 raw1404Labels = mixedMoment B node4570 node4570Labels := by
  calc
    mixedMoment B raw1404 raw1404Labels = mixedMoment B raw1404step0 raw1404step0Labels := by
      have ha : raw1404step0 = (fun i j => raw1404 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1404step0 raw1404; decide +kernel
      have hl : raw1404step0Labels = raw1404Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1404 raw1404Labels permutation32 permutation4
    mixedMoment B raw1404step0 raw1404step0Labels = mixedMoment B raw1404step1 raw1404step1Labels := by
      have ha : raw1404step1 = raw1404step0 := by apply Matrix.ext; unfold raw1404step1 raw1404step0; decide +kernel
      have hl : raw1404step0Labels = labelEmbedding7 ∘ raw1404step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1404step0 raw1404step0Labels raw1404step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4570 node4570Labels := by rfl

def raw1405 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1405Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw1405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1405 raw1405Labels = mixedMoment B node1188 node1188Labels := by
  calc
    mixedMoment B raw1405 raw1405Labels = mixedMoment B raw1405step0 raw1405step0Labels := by
      have ha : raw1405step0 = (fun i j => raw1405 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1405step0 raw1405; decide +kernel
      have hl : raw1405step0Labels = raw1405Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1405 raw1405Labels permutation32 permutation4
    _ = mixedMoment B node1188 node1188Labels := by rfl

def raw1406 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2]]
def raw1406Labels : Fin 3 → Fin 2 := ![1, 0, 1]

def raw1406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw1406step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1406step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw1406step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw1406step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical1406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1406 raw1406Labels = mixedMoment B node3245 node3245Labels := by
  calc
    mixedMoment B raw1406 raw1406Labels = mixedMoment B raw1406step0 raw1406step0Labels := by
      have ha : raw1406step0 = (fun i j => raw1406 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw1406step0 raw1406; decide +kernel
      have hl : raw1406step0Labels = raw1406Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1406 raw1406Labels permutation32 permutation6
    mixedMoment B raw1406step0 raw1406step0Labels = mixedMoment B raw1406step1 raw1406step1Labels := by
      have ha : raw1406step1 = -raw1406step0 := by apply Matrix.ext; change ∀ i j, raw1406step1 i j = -(raw1406step0 i j); unfold raw1406step1 raw1406step0; decide +kernel
      have hl : raw1406step1Labels = raw1406step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw1406step1 raw1406step1Labels = mixedMoment B raw1406step2 raw1406step2Labels := by
      have ha : raw1406step2 = raw1406step1 := by apply Matrix.ext; unfold raw1406step2 raw1406step1; decide +kernel
      have hl : raw1406step1Labels = labelEmbedding1 ∘ raw1406step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1406step1 raw1406step1Labels raw1406step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3245 node3245Labels := by rfl

def raw1407 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -4, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 3, -3]]
def raw1407Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw1407step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw1407step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw1407step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw1407step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical1407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw1407 raw1407Labels = mixedMoment B node4572 node4572Labels := by
  calc
    mixedMoment B raw1407 raw1407Labels = mixedMoment B raw1407step0 raw1407step0Labels := by
      have ha : raw1407step0 = (fun i j => raw1407 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw1407step0 raw1407; decide +kernel
      have hl : raw1407step0Labels = raw1407Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw1407 raw1407Labels permutation8 permutation4
    mixedMoment B raw1407step0 raw1407step0Labels = mixedMoment B raw1407step1 raw1407step1Labels := by
      have ha : raw1407step1 = raw1407step0 := by apply Matrix.ext; unfold raw1407step1 raw1407step0; decide +kernel
      have hl : raw1407step0Labels = labelEmbedding7 ∘ raw1407step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw1407step0 raw1407step0Labels raw1407step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4572 node4572Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
