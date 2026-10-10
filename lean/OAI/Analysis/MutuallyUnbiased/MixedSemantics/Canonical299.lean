import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw38272 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![4, -2, -2]]
def raw38272Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38272step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, 0, 1], ![-2, -2, 4]]
def raw38272step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38272step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]
def raw38272step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38272step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 0, -1], ![2, 2, -4]]
def raw38272step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38272 raw38272Labels = mixedMoment B node1537 node1537Labels := by
  calc
    mixedMoment B raw38272 raw38272Labels = mixedMoment B raw38272step0 raw38272step0Labels := by
      have ha : raw38272step0 = (fun i j => raw38272 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38272step0 raw38272; decide +kernel
      have hl : raw38272step0Labels = raw38272Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38272 raw38272Labels permutation2 permutation7
    mixedMoment B raw38272step0 raw38272step0Labels = mixedMoment B raw38272step1 raw38272step1Labels := by
      have ha : raw38272step1 = -raw38272step0 := by apply Matrix.ext; change ∀ i j, raw38272step1 i j = -(raw38272step0 i j); unfold raw38272step1 raw38272step0; decide +kernel
      have hl : raw38272step1Labels = raw38272step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38272step1 raw38272step1Labels = mixedMoment B raw38272step2 raw38272step2Labels := by
      have ha : raw38272step2 = raw38272step1 := by apply Matrix.ext; unfold raw38272step2 raw38272step1; decide +kernel
      have hl : raw38272step1Labels = labelEmbedding4 ∘ raw38272step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38272step1 raw38272step1Labels raw38272step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1537 node1537Labels := by rfl

def raw38273 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw38273Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38273step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw38273step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38273 raw38273Labels = mixedMoment B node618 node618Labels := by
  calc
    mixedMoment B raw38273 raw38273Labels = mixedMoment B raw38273step0 raw38273step0Labels := by
      have ha : raw38273step0 = raw38273 := by apply Matrix.ext; unfold raw38273step0 raw38273; decide +kernel
      have hl : raw38273Labels = labelEmbedding2 ∘ raw38273step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38273 raw38273Labels raw38273step0Labels labelEmbedding2 hl
    _ = mixedMoment B node618 node618Labels := by rfl

def raw38274 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -2, 0], ![3, 0, -3]]
def raw38274Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38274step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-3, 0, 3]]
def raw38274step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38274step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def raw38274step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38274step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![3, 0, -3]]
def raw38274step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38274 raw38274Labels = mixedMoment B node1527 node1527Labels := by
  calc
    mixedMoment B raw38274 raw38274Labels = mixedMoment B raw38274step0 raw38274step0Labels := by
      have ha : raw38274step0 = (fun i j => raw38274 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38274step0 raw38274; decide +kernel
      have hl : raw38274step0Labels = raw38274Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38274 raw38274Labels permutation2 permutation7
    mixedMoment B raw38274step0 raw38274step0Labels = mixedMoment B raw38274step1 raw38274step1Labels := by
      have ha : raw38274step1 = -raw38274step0 := by apply Matrix.ext; change ∀ i j, raw38274step1 i j = -(raw38274step0 i j); unfold raw38274step1 raw38274step0; decide +kernel
      have hl : raw38274step1Labels = raw38274step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38274step1 raw38274step1Labels = mixedMoment B raw38274step2 raw38274step2Labels := by
      have ha : raw38274step2 = raw38274step1 := by apply Matrix.ext; unfold raw38274step2 raw38274step1; decide +kernel
      have hl : raw38274step1Labels = labelEmbedding4 ∘ raw38274step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38274step1 raw38274step1Labels raw38274step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1527 node1527Labels := by rfl

def raw38275 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw38275Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38275step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw38275step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38275 raw38275Labels = mixedMoment B node619 node619Labels := by
  calc
    mixedMoment B raw38275 raw38275Labels = mixedMoment B raw38275step0 raw38275step0Labels := by
      have ha : raw38275step0 = raw38275 := by apply Matrix.ext; unfold raw38275step0 raw38275; decide +kernel
      have hl : raw38275Labels = labelEmbedding2 ∘ raw38275step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38275 raw38275Labels raw38275step0Labels labelEmbedding2 hl
    _ = mixedMoment B node619 node619Labels := by rfl

def raw38276 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw38276Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38276step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -1, 2], ![-2, -1, 3]]
def raw38276step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38276step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def raw38276step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38276step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 1, -2], ![2, 1, -3]]
def raw38276step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38276 raw38276Labels = mixedMoment B node1538 node1538Labels := by
  calc
    mixedMoment B raw38276 raw38276Labels = mixedMoment B raw38276step0 raw38276step0Labels := by
      have ha : raw38276step0 = (fun i j => raw38276 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38276step0 raw38276; decide +kernel
      have hl : raw38276step0Labels = raw38276Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38276 raw38276Labels permutation2 permutation7
    mixedMoment B raw38276step0 raw38276step0Labels = mixedMoment B raw38276step1 raw38276step1Labels := by
      have ha : raw38276step1 = -raw38276step0 := by apply Matrix.ext; change ∀ i j, raw38276step1 i j = -(raw38276step0 i j); unfold raw38276step1 raw38276step0; decide +kernel
      have hl : raw38276step1Labels = raw38276step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38276step1 raw38276step1Labels = mixedMoment B raw38276step2 raw38276step2Labels := by
      have ha : raw38276step2 = raw38276step1 := by apply Matrix.ext; unfold raw38276step2 raw38276step1; decide +kernel
      have hl : raw38276step1Labels = labelEmbedding4 ∘ raw38276step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38276step1 raw38276step1Labels raw38276step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1538 node1538Labels := by rfl

def raw38277 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw38277Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38277step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw38277step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38277 raw38277Labels = mixedMoment B node620 node620Labels := by
  calc
    mixedMoment B raw38277 raw38277Labels = mixedMoment B raw38277step0 raw38277step0Labels := by
      have ha : raw38277step0 = raw38277 := by apply Matrix.ext; unfold raw38277step0 raw38277; decide +kernel
      have hl : raw38277Labels = labelEmbedding2 ∘ raw38277step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38277 raw38277Labels raw38277step0Labels labelEmbedding2 hl
    _ = mixedMoment B node620 node620Labels := by rfl

def raw38278 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw38278Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38278step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 2, -5], ![-1, -2, 3], ![-2, 0, 2]]
def raw38278step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38278step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![2, 0, -2]]
def raw38278step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38278step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -2, 5], ![1, 2, -3], ![2, 0, -2]]
def raw38278step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38278 raw38278Labels = mixedMoment B node1539 node1539Labels := by
  calc
    mixedMoment B raw38278 raw38278Labels = mixedMoment B raw38278step0 raw38278step0Labels := by
      have ha : raw38278step0 = (fun i j => raw38278 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38278step0 raw38278; decide +kernel
      have hl : raw38278step0Labels = raw38278Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38278 raw38278Labels permutation3 permutation7
    mixedMoment B raw38278step0 raw38278step0Labels = mixedMoment B raw38278step1 raw38278step1Labels := by
      have ha : raw38278step1 = -raw38278step0 := by apply Matrix.ext; change ∀ i j, raw38278step1 i j = -(raw38278step0 i j); unfold raw38278step1 raw38278step0; decide +kernel
      have hl : raw38278step1Labels = raw38278step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38278step1 raw38278step1Labels = mixedMoment B raw38278step2 raw38278step2Labels := by
      have ha : raw38278step2 = raw38278step1 := by apply Matrix.ext; unfold raw38278step2 raw38278step1; decide +kernel
      have hl : raw38278step1Labels = labelEmbedding4 ∘ raw38278step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38278step1 raw38278step1Labels raw38278step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1539 node1539Labels := by rfl

def raw38279 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw38279Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38279step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw38279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38279 raw38279Labels = mixedMoment B node622 node622Labels := by
  calc
    mixedMoment B raw38279 raw38279Labels = mixedMoment B raw38279step0 raw38279step0Labels := by
      have ha : raw38279step0 = raw38279 := by apply Matrix.ext; unfold raw38279step0 raw38279; decide +kernel
      have hl : raw38279Labels = labelEmbedding2 ∘ raw38279step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38279 raw38279Labels raw38279step0Labels labelEmbedding2 hl
    _ = mixedMoment B node622 node622Labels := by rfl

def raw38280 : Matrix (Fin 2) (Fin 3) ℤ := ![![-5, 2, 3], ![5, -2, -3]]
def raw38280Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38280step0 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -2, 5], ![3, 2, -5]]
def raw38280step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38280step1 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, -2, 5], ![3, 2, -5]]
def raw38280step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38280 raw38280Labels = mixedMoment B node1541 node1541Labels := by
  calc
    mixedMoment B raw38280 raw38280Labels = mixedMoment B raw38280step0 raw38280step0Labels := by
      have ha : raw38280step0 = (fun i j => raw38280 (permutation1 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38280step0 raw38280; decide +kernel
      have hl : raw38280step0Labels = raw38280Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38280 raw38280Labels permutation1 permutation7
    mixedMoment B raw38280step0 raw38280step0Labels = mixedMoment B raw38280step1 raw38280step1Labels := by
      have ha : raw38280step1 = raw38280step0 := by apply Matrix.ext; unfold raw38280step1 raw38280step0; decide +kernel
      have hl : raw38280step0Labels = labelEmbedding4 ∘ raw38280step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38280step0 raw38280step0Labels raw38280step1Labels labelEmbedding4 hl
    _ = mixedMoment B node1541 node1541Labels := by rfl

def raw38281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38281Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38281step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38281 raw38281Labels = mixedMoment B node698 node698Labels := by
  calc
    mixedMoment B raw38281 raw38281Labels = mixedMoment B raw38281step0 raw38281step0Labels := by
      have ha : raw38281step0 = raw38281 := by apply Matrix.ext; unfold raw38281step0 raw38281; decide +kernel
      have hl : raw38281Labels = labelEmbedding2 ∘ raw38281step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38281 raw38281Labels raw38281step0Labels labelEmbedding2 hl
    _ = mixedMoment B node698 node698Labels := by rfl

def raw38282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38282Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw38282step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38282step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw38282step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38282step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw38282step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38282 raw38282Labels = mixedMoment B node744 node744Labels := by
  calc
    mixedMoment B raw38282 raw38282Labels = mixedMoment B raw38282step0 raw38282step0Labels := by
      have ha : raw38282step0 = (fun i j => raw38282 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38282step0 raw38282; decide +kernel
      have hl : raw38282step0Labels = raw38282Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38282 raw38282Labels permutation160 permutation7
    mixedMoment B raw38282step0 raw38282step0Labels = mixedMoment B raw38282step1 raw38282step1Labels := by
      have ha : raw38282step1 = -raw38282step0 := by apply Matrix.ext; change ∀ i j, raw38282step1 i j = -(raw38282step0 i j); unfold raw38282step1 raw38282step0; decide +kernel
      have hl : raw38282step1Labels = raw38282step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38282step1 raw38282step1Labels = mixedMoment B raw38282step2 raw38282step2Labels := by
      have ha : raw38282step2 = raw38282step1 := by apply Matrix.ext; unfold raw38282step2 raw38282step1; decide +kernel
      have hl : raw38282step1Labels = labelEmbedding4 ∘ raw38282step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38282step1 raw38282step1Labels raw38282step2Labels labelEmbedding4 hl
    _ = mixedMoment B node744 node744Labels := by rfl

def raw38283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38283Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38283step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38283step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38283 raw38283Labels = mixedMoment B node699 node699Labels := by
  calc
    mixedMoment B raw38283 raw38283Labels = mixedMoment B raw38283step0 raw38283step0Labels := by
      have ha : raw38283step0 = raw38283 := by apply Matrix.ext; unfold raw38283step0 raw38283; decide +kernel
      have hl : raw38283Labels = labelEmbedding2 ∘ raw38283step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38283 raw38283Labels raw38283step0Labels labelEmbedding2 hl
    _ = mixedMoment B node699 node699Labels := by rfl

def raw38284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38284Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw38284step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38284step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38284step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38284step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38284 raw38284Labels = mixedMoment B node748 node748Labels := by
  calc
    mixedMoment B raw38284 raw38284Labels = mixedMoment B raw38284step0 raw38284step0Labels := by
      have ha : raw38284step0 = (fun i j => raw38284 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38284step0 raw38284; decide +kernel
      have hl : raw38284step0Labels = raw38284Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38284 raw38284Labels permutation158 permutation7
    mixedMoment B raw38284step0 raw38284step0Labels = mixedMoment B raw38284step1 raw38284step1Labels := by
      have ha : raw38284step1 = -raw38284step0 := by apply Matrix.ext; change ∀ i j, raw38284step1 i j = -(raw38284step0 i j); unfold raw38284step1 raw38284step0; decide +kernel
      have hl : raw38284step1Labels = raw38284step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38284step1 raw38284step1Labels = mixedMoment B raw38284step2 raw38284step2Labels := by
      have ha : raw38284step2 = raw38284step1 := by apply Matrix.ext; unfold raw38284step2 raw38284step1; decide +kernel
      have hl : raw38284step1Labels = labelEmbedding4 ∘ raw38284step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38284step1 raw38284step1Labels raw38284step2Labels labelEmbedding4 hl
    _ = mixedMoment B node748 node748Labels := by rfl

def raw38285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38285Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38285step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38285 raw38285Labels = mixedMoment B node700 node700Labels := by
  calc
    mixedMoment B raw38285 raw38285Labels = mixedMoment B raw38285step0 raw38285step0Labels := by
      have ha : raw38285step0 = raw38285 := by apply Matrix.ext; unfold raw38285step0 raw38285; decide +kernel
      have hl : raw38285Labels = labelEmbedding2 ∘ raw38285step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38285 raw38285Labels raw38285step0Labels labelEmbedding2 hl
    _ = mixedMoment B node700 node700Labels := by rfl

def raw38286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38286Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw38286step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38286step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38286step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38286step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38286 raw38286Labels = mixedMoment B node749 node749Labels := by
  calc
    mixedMoment B raw38286 raw38286Labels = mixedMoment B raw38286step0 raw38286step0Labels := by
      have ha : raw38286step0 = (fun i j => raw38286 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38286step0 raw38286; decide +kernel
      have hl : raw38286step0Labels = raw38286Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38286 raw38286Labels permutation158 permutation7
    mixedMoment B raw38286step0 raw38286step0Labels = mixedMoment B raw38286step1 raw38286step1Labels := by
      have ha : raw38286step1 = -raw38286step0 := by apply Matrix.ext; change ∀ i j, raw38286step1 i j = -(raw38286step0 i j); unfold raw38286step1 raw38286step0; decide +kernel
      have hl : raw38286step1Labels = raw38286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38286step1 raw38286step1Labels = mixedMoment B raw38286step2 raw38286step2Labels := by
      have ha : raw38286step2 = raw38286step1 := by apply Matrix.ext; unfold raw38286step2 raw38286step1; decide +kernel
      have hl : raw38286step1Labels = labelEmbedding4 ∘ raw38286step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38286step1 raw38286step1Labels raw38286step2Labels labelEmbedding4 hl
    _ = mixedMoment B node749 node749Labels := by rfl

def raw38287 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw38287Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw38287step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38287 raw38287Labels = mixedMoment B node701 node701Labels := by
  calc
    mixedMoment B raw38287 raw38287Labels = mixedMoment B raw38287step0 raw38287step0Labels := by
      have ha : raw38287step0 = raw38287 := by apply Matrix.ext; unfold raw38287step0 raw38287; decide +kernel
      have hl : raw38287Labels = labelEmbedding2 ∘ raw38287step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38287 raw38287Labels raw38287step0Labels labelEmbedding2 hl
    _ = mixedMoment B node701 node701Labels := by rfl

def raw38288 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw38288Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, -1, 4]]
def raw38288step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw38288step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw38288step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38288 raw38288Labels = mixedMoment B node750 node750Labels := by
  calc
    mixedMoment B raw38288 raw38288Labels = mixedMoment B raw38288step0 raw38288step0Labels := by
      have ha : raw38288step0 = (fun i j => raw38288 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38288step0 raw38288; decide +kernel
      have hl : raw38288step0Labels = raw38288Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38288 raw38288Labels permutation34 permutation7
    mixedMoment B raw38288step0 raw38288step0Labels = mixedMoment B raw38288step1 raw38288step1Labels := by
      have ha : raw38288step1 = -raw38288step0 := by apply Matrix.ext; change ∀ i j, raw38288step1 i j = -(raw38288step0 i j); unfold raw38288step1 raw38288step0; decide +kernel
      have hl : raw38288step1Labels = raw38288step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38288step1 raw38288step1Labels = mixedMoment B raw38288step2 raw38288step2Labels := by
      have ha : raw38288step2 = raw38288step1 := by apply Matrix.ext; unfold raw38288step2 raw38288step1; decide +kernel
      have hl : raw38288step1Labels = labelEmbedding4 ∘ raw38288step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38288step1 raw38288step1Labels raw38288step2Labels labelEmbedding4 hl
    _ = mixedMoment B node750 node750Labels := by rfl

def raw38289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38289Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38289step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38289 raw38289Labels = mixedMoment B node702 node702Labels := by
  calc
    mixedMoment B raw38289 raw38289Labels = mixedMoment B raw38289step0 raw38289step0Labels := by
      have ha : raw38289step0 = raw38289 := by apply Matrix.ext; unfold raw38289step0 raw38289; decide +kernel
      have hl : raw38289Labels = labelEmbedding2 ∘ raw38289step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38289 raw38289Labels raw38289step0Labels labelEmbedding2 hl
    _ = mixedMoment B node702 node702Labels := by rfl

def raw38290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38290Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw38290step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38290step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38290step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38290step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38290step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38290 raw38290Labels = mixedMoment B node760 node760Labels := by
  calc
    mixedMoment B raw38290 raw38290Labels = mixedMoment B raw38290step0 raw38290step0Labels := by
      have ha : raw38290step0 = (fun i j => raw38290 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38290step0 raw38290; decide +kernel
      have hl : raw38290step0Labels = raw38290Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38290 raw38290Labels permutation152 permutation7
    mixedMoment B raw38290step0 raw38290step0Labels = mixedMoment B raw38290step1 raw38290step1Labels := by
      have ha : raw38290step1 = -raw38290step0 := by apply Matrix.ext; change ∀ i j, raw38290step1 i j = -(raw38290step0 i j); unfold raw38290step1 raw38290step0; decide +kernel
      have hl : raw38290step1Labels = raw38290step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38290step1 raw38290step1Labels = mixedMoment B raw38290step2 raw38290step2Labels := by
      have ha : raw38290step2 = raw38290step1 := by apply Matrix.ext; unfold raw38290step2 raw38290step1; decide +kernel
      have hl : raw38290step1Labels = labelEmbedding4 ∘ raw38290step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38290step1 raw38290step1Labels raw38290step2Labels labelEmbedding4 hl
    _ = mixedMoment B node760 node760Labels := by rfl

def raw38291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38291Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38291step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38291 raw38291Labels = mixedMoment B node703 node703Labels := by
  calc
    mixedMoment B raw38291 raw38291Labels = mixedMoment B raw38291step0 raw38291step0Labels := by
      have ha : raw38291step0 = raw38291 := by apply Matrix.ext; unfold raw38291step0 raw38291; decide +kernel
      have hl : raw38291Labels = labelEmbedding2 ∘ raw38291step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38291 raw38291Labels raw38291step0Labels labelEmbedding2 hl
    _ = mixedMoment B node703 node703Labels := by rfl

def raw38292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38292Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw38292step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38292step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38292step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38292step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38292step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38292 raw38292Labels = mixedMoment B node754 node754Labels := by
  calc
    mixedMoment B raw38292 raw38292Labels = mixedMoment B raw38292step0 raw38292step0Labels := by
      have ha : raw38292step0 = (fun i j => raw38292 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38292step0 raw38292; decide +kernel
      have hl : raw38292step0Labels = raw38292Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38292 raw38292Labels permutation164 permutation7
    mixedMoment B raw38292step0 raw38292step0Labels = mixedMoment B raw38292step1 raw38292step1Labels := by
      have ha : raw38292step1 = -raw38292step0 := by apply Matrix.ext; change ∀ i j, raw38292step1 i j = -(raw38292step0 i j); unfold raw38292step1 raw38292step0; decide +kernel
      have hl : raw38292step1Labels = raw38292step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38292step1 raw38292step1Labels = mixedMoment B raw38292step2 raw38292step2Labels := by
      have ha : raw38292step2 = raw38292step1 := by apply Matrix.ext; unfold raw38292step2 raw38292step1; decide +kernel
      have hl : raw38292step1Labels = labelEmbedding4 ∘ raw38292step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38292step1 raw38292step1Labels raw38292step2Labels labelEmbedding4 hl
    _ = mixedMoment B node754 node754Labels := by rfl

def raw38293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38293Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38293step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38293step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38293 raw38293Labels = mixedMoment B node704 node704Labels := by
  calc
    mixedMoment B raw38293 raw38293Labels = mixedMoment B raw38293step0 raw38293step0Labels := by
      have ha : raw38293step0 = raw38293 := by apply Matrix.ext; unfold raw38293step0 raw38293; decide +kernel
      have hl : raw38293Labels = labelEmbedding2 ∘ raw38293step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38293 raw38293Labels raw38293step0Labels labelEmbedding2 hl
    _ = mixedMoment B node704 node704Labels := by rfl

def raw38294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38294Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw38294step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38294step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38294step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38294step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38294step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38294 raw38294Labels = mixedMoment B node761 node761Labels := by
  calc
    mixedMoment B raw38294 raw38294Labels = mixedMoment B raw38294step0 raw38294step0Labels := by
      have ha : raw38294step0 = (fun i j => raw38294 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38294step0 raw38294; decide +kernel
      have hl : raw38294step0Labels = raw38294Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38294 raw38294Labels permutation152 permutation7
    mixedMoment B raw38294step0 raw38294step0Labels = mixedMoment B raw38294step1 raw38294step1Labels := by
      have ha : raw38294step1 = -raw38294step0 := by apply Matrix.ext; change ∀ i j, raw38294step1 i j = -(raw38294step0 i j); unfold raw38294step1 raw38294step0; decide +kernel
      have hl : raw38294step1Labels = raw38294step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38294step1 raw38294step1Labels = mixedMoment B raw38294step2 raw38294step2Labels := by
      have ha : raw38294step2 = raw38294step1 := by apply Matrix.ext; unfold raw38294step2 raw38294step1; decide +kernel
      have hl : raw38294step1Labels = labelEmbedding4 ∘ raw38294step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38294step1 raw38294step1Labels raw38294step2Labels labelEmbedding4 hl
    _ = mixedMoment B node761 node761Labels := by rfl

def raw38295 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw38295Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw38295step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38295 raw38295Labels = mixedMoment B node705 node705Labels := by
  calc
    mixedMoment B raw38295 raw38295Labels = mixedMoment B raw38295step0 raw38295step0Labels := by
      have ha : raw38295step0 = raw38295 := by apply Matrix.ext; unfold raw38295step0 raw38295; decide +kernel
      have hl : raw38295Labels = labelEmbedding2 ∘ raw38295step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38295 raw38295Labels raw38295step0Labels labelEmbedding2 hl
    _ = mixedMoment B node705 node705Labels := by rfl

def raw38296 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw38296Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -2, 4]]
def raw38296step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw38296step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38296step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 2, -4]]
def raw38296step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38296 raw38296Labels = mixedMoment B node762 node762Labels := by
  calc
    mixedMoment B raw38296 raw38296Labels = mixedMoment B raw38296step0 raw38296step0Labels := by
      have ha : raw38296step0 = (fun i j => raw38296 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38296step0 raw38296; decide +kernel
      have hl : raw38296step0Labels = raw38296Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38296 raw38296Labels permutation32 permutation7
    mixedMoment B raw38296step0 raw38296step0Labels = mixedMoment B raw38296step1 raw38296step1Labels := by
      have ha : raw38296step1 = -raw38296step0 := by apply Matrix.ext; change ∀ i j, raw38296step1 i j = -(raw38296step0 i j); unfold raw38296step1 raw38296step0; decide +kernel
      have hl : raw38296step1Labels = raw38296step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38296step1 raw38296step1Labels = mixedMoment B raw38296step2 raw38296step2Labels := by
      have ha : raw38296step2 = raw38296step1 := by apply Matrix.ext; unfold raw38296step2 raw38296step1; decide +kernel
      have hl : raw38296step1Labels = labelEmbedding4 ∘ raw38296step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38296step1 raw38296step1Labels raw38296step2Labels labelEmbedding4 hl
    _ = mixedMoment B node762 node762Labels := by rfl

def raw38297 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw38297Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw38297step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38297 raw38297Labels = mixedMoment B node706 node706Labels := by
  calc
    mixedMoment B raw38297 raw38297Labels = mixedMoment B raw38297step0 raw38297step0Labels := by
      have ha : raw38297step0 = raw38297 := by apply Matrix.ext; unfold raw38297step0 raw38297; decide +kernel
      have hl : raw38297Labels = labelEmbedding2 ∘ raw38297step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38297 raw38297Labels raw38297step0Labels labelEmbedding2 hl
    _ = mixedMoment B node706 node706Labels := by rfl

def raw38298 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw38298Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 0, 3]]
def raw38298step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw38298step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38298step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, 0, -3]]
def raw38298step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38298 raw38298Labels = mixedMoment B node755 node755Labels := by
  calc
    mixedMoment B raw38298 raw38298Labels = mixedMoment B raw38298step0 raw38298step0Labels := by
      have ha : raw38298step0 = (fun i j => raw38298 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38298step0 raw38298; decide +kernel
      have hl : raw38298step0Labels = raw38298Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38298 raw38298Labels permutation34 permutation7
    mixedMoment B raw38298step0 raw38298step0Labels = mixedMoment B raw38298step1 raw38298step1Labels := by
      have ha : raw38298step1 = -raw38298step0 := by apply Matrix.ext; change ∀ i j, raw38298step1 i j = -(raw38298step0 i j); unfold raw38298step1 raw38298step0; decide +kernel
      have hl : raw38298step1Labels = raw38298step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38298step1 raw38298step1Labels = mixedMoment B raw38298step2 raw38298step2Labels := by
      have ha : raw38298step2 = raw38298step1 := by apply Matrix.ext; unfold raw38298step2 raw38298step1; decide +kernel
      have hl : raw38298step1Labels = labelEmbedding4 ∘ raw38298step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38298step1 raw38298step1Labels raw38298step2Labels labelEmbedding4 hl
    _ = mixedMoment B node755 node755Labels := by rfl

def raw38299 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38299Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38299step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38299 raw38299Labels = mixedMoment B node707 node707Labels := by
  calc
    mixedMoment B raw38299 raw38299Labels = mixedMoment B raw38299step0 raw38299step0Labels := by
      have ha : raw38299step0 = raw38299 := by apply Matrix.ext; unfold raw38299step0 raw38299; decide +kernel
      have hl : raw38299Labels = labelEmbedding2 ∘ raw38299step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38299 raw38299Labels raw38299step0Labels labelEmbedding2 hl
    _ = mixedMoment B node707 node707Labels := by rfl

def raw38300 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38300Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, -1, 3]]
def raw38300step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw38300step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38300step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw38300step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38300 raw38300Labels = mixedMoment B node763 node763Labels := by
  calc
    mixedMoment B raw38300 raw38300Labels = mixedMoment B raw38300step0 raw38300step0Labels := by
      have ha : raw38300step0 = (fun i j => raw38300 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38300step0 raw38300; decide +kernel
      have hl : raw38300step0Labels = raw38300Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38300 raw38300Labels permutation32 permutation7
    mixedMoment B raw38300step0 raw38300step0Labels = mixedMoment B raw38300step1 raw38300step1Labels := by
      have ha : raw38300step1 = -raw38300step0 := by apply Matrix.ext; change ∀ i j, raw38300step1 i j = -(raw38300step0 i j); unfold raw38300step1 raw38300step0; decide +kernel
      have hl : raw38300step1Labels = raw38300step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38300step1 raw38300step1Labels = mixedMoment B raw38300step2 raw38300step2Labels := by
      have ha : raw38300step2 = raw38300step1 := by apply Matrix.ext; unfold raw38300step2 raw38300step1; decide +kernel
      have hl : raw38300step1Labels = labelEmbedding4 ∘ raw38300step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38300step1 raw38300step1Labels raw38300step2Labels labelEmbedding4 hl
    _ = mixedMoment B node763 node763Labels := by rfl

def raw38301 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38301Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38301step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38301 raw38301Labels = mixedMoment B node708 node708Labels := by
  calc
    mixedMoment B raw38301 raw38301Labels = mixedMoment B raw38301step0 raw38301step0Labels := by
      have ha : raw38301step0 = raw38301 := by apply Matrix.ext; unfold raw38301step0 raw38301; decide +kernel
      have hl : raw38301Labels = labelEmbedding2 ∘ raw38301step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38301 raw38301Labels raw38301step0Labels labelEmbedding2 hl
    _ = mixedMoment B node708 node708Labels := by rfl

def raw38302 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38302Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 0, 2]]
def raw38302step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw38302step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38302step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, 0, -2]]
def raw38302step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38302 raw38302Labels = mixedMoment B node764 node764Labels := by
  calc
    mixedMoment B raw38302 raw38302Labels = mixedMoment B raw38302step0 raw38302step0Labels := by
      have ha : raw38302step0 = (fun i j => raw38302 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38302step0 raw38302; decide +kernel
      have hl : raw38302step0Labels = raw38302Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38302 raw38302Labels permutation33 permutation7
    mixedMoment B raw38302step0 raw38302step0Labels = mixedMoment B raw38302step1 raw38302step1Labels := by
      have ha : raw38302step1 = -raw38302step0 := by apply Matrix.ext; change ∀ i j, raw38302step1 i j = -(raw38302step0 i j); unfold raw38302step1 raw38302step0; decide +kernel
      have hl : raw38302step1Labels = raw38302step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38302step1 raw38302step1Labels = mixedMoment B raw38302step2 raw38302step2Labels := by
      have ha : raw38302step2 = raw38302step1 := by apply Matrix.ext; unfold raw38302step2 raw38302step1; decide +kernel
      have hl : raw38302step1Labels = labelEmbedding4 ∘ raw38302step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38302step1 raw38302step1Labels raw38302step2Labels labelEmbedding4 hl
    _ = mixedMoment B node764 node764Labels := by rfl

def raw38303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38303Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38303step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38303 raw38303Labels = mixedMoment B node709 node709Labels := by
  calc
    mixedMoment B raw38303 raw38303Labels = mixedMoment B raw38303step0 raw38303step0Labels := by
      have ha : raw38303step0 = raw38303 := by apply Matrix.ext; unfold raw38303step0 raw38303; decide +kernel
      have hl : raw38303Labels = labelEmbedding2 ∘ raw38303step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38303 raw38303Labels raw38303step0Labels labelEmbedding2 hl
    _ = mixedMoment B node709 node709Labels := by rfl

def raw38304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38304Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38304step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw38304step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38304step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38304step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38304step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw38304step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38304 raw38304Labels = mixedMoment B node745 node745Labels := by
  calc
    mixedMoment B raw38304 raw38304Labels = mixedMoment B raw38304step0 raw38304step0Labels := by
      have ha : raw38304step0 = (fun i j => raw38304 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38304step0 raw38304; decide +kernel
      have hl : raw38304step0Labels = raw38304Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38304 raw38304Labels permutation152 permutation7
    mixedMoment B raw38304step0 raw38304step0Labels = mixedMoment B raw38304step1 raw38304step1Labels := by
      have ha : raw38304step1 = -raw38304step0 := by apply Matrix.ext; change ∀ i j, raw38304step1 i j = -(raw38304step0 i j); unfold raw38304step1 raw38304step0; decide +kernel
      have hl : raw38304step1Labels = raw38304step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38304step1 raw38304step1Labels = mixedMoment B raw38304step2 raw38304step2Labels := by
      have ha : raw38304step2 = raw38304step1 := by apply Matrix.ext; unfold raw38304step2 raw38304step1; decide +kernel
      have hl : raw38304step1Labels = labelEmbedding4 ∘ raw38304step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38304step1 raw38304step1Labels raw38304step2Labels labelEmbedding4 hl
    _ = mixedMoment B node745 node745Labels := by rfl

def raw38305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38305Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38305step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38305 raw38305Labels = mixedMoment B node710 node710Labels := by
  calc
    mixedMoment B raw38305 raw38305Labels = mixedMoment B raw38305step0 raw38305step0Labels := by
      have ha : raw38305step0 = raw38305 := by apply Matrix.ext; unfold raw38305step0 raw38305; decide +kernel
      have hl : raw38305Labels = labelEmbedding2 ∘ raw38305step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38305 raw38305Labels raw38305step0Labels labelEmbedding2 hl
    _ = mixedMoment B node710 node710Labels := by rfl

def raw38306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw38306Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38306step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw38306step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38306step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38306step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38306step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw38306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38306 raw38306Labels = mixedMoment B node746 node746Labels := by
  calc
    mixedMoment B raw38306 raw38306Labels = mixedMoment B raw38306step0 raw38306step0Labels := by
      have ha : raw38306step0 = (fun i j => raw38306 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38306step0 raw38306; decide +kernel
      have hl : raw38306step0Labels = raw38306Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38306 raw38306Labels permutation152 permutation7
    mixedMoment B raw38306step0 raw38306step0Labels = mixedMoment B raw38306step1 raw38306step1Labels := by
      have ha : raw38306step1 = -raw38306step0 := by apply Matrix.ext; change ∀ i j, raw38306step1 i j = -(raw38306step0 i j); unfold raw38306step1 raw38306step0; decide +kernel
      have hl : raw38306step1Labels = raw38306step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38306step1 raw38306step1Labels = mixedMoment B raw38306step2 raw38306step2Labels := by
      have ha : raw38306step2 = raw38306step1 := by apply Matrix.ext; unfold raw38306step2 raw38306step1; decide +kernel
      have hl : raw38306step1Labels = labelEmbedding4 ∘ raw38306step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38306step1 raw38306step1Labels raw38306step2Labels labelEmbedding4 hl
    _ = mixedMoment B node746 node746Labels := by rfl

def raw38307 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw38307Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw38307step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38307 raw38307Labels = mixedMoment B node711 node711Labels := by
  calc
    mixedMoment B raw38307 raw38307Labels = mixedMoment B raw38307step0 raw38307step0Labels := by
      have ha : raw38307step0 = raw38307 := by apply Matrix.ext; unfold raw38307step0 raw38307; decide +kernel
      have hl : raw38307Labels = labelEmbedding2 ∘ raw38307step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38307 raw38307Labels raw38307step0Labels labelEmbedding2 hl
    _ = mixedMoment B node711 node711Labels := by rfl

def raw38308 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw38308Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-4, 1, 3]]
def raw38308step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -1, -3]]
def raw38308step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38308step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![4, -1, -3]]
def raw38308step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38308 raw38308Labels = mixedMoment B node747 node747Labels := by
  calc
    mixedMoment B raw38308 raw38308Labels = mixedMoment B raw38308step0 raw38308step0Labels := by
      have ha : raw38308step0 = (fun i j => raw38308 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38308step0 raw38308; decide +kernel
      have hl : raw38308step0Labels = raw38308Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38308 raw38308Labels permutation32 permutation7
    mixedMoment B raw38308step0 raw38308step0Labels = mixedMoment B raw38308step1 raw38308step1Labels := by
      have ha : raw38308step1 = -raw38308step0 := by apply Matrix.ext; change ∀ i j, raw38308step1 i j = -(raw38308step0 i j); unfold raw38308step1 raw38308step0; decide +kernel
      have hl : raw38308step1Labels = raw38308step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38308step1 raw38308step1Labels = mixedMoment B raw38308step2 raw38308step2Labels := by
      have ha : raw38308step2 = raw38308step1 := by apply Matrix.ext; unfold raw38308step2 raw38308step1; decide +kernel
      have hl : raw38308step1Labels = labelEmbedding4 ∘ raw38308step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38308step1 raw38308step1Labels raw38308step2Labels labelEmbedding4 hl
    _ = mixedMoment B node747 node747Labels := by rfl

def raw38309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38309Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38309step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38309step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38309 raw38309Labels = mixedMoment B node713 node713Labels := by
  calc
    mixedMoment B raw38309 raw38309Labels = mixedMoment B raw38309step0 raw38309step0Labels := by
      have ha : raw38309step0 = raw38309 := by apply Matrix.ext; unfold raw38309step0 raw38309; decide +kernel
      have hl : raw38309Labels = labelEmbedding2 ∘ raw38309step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38309 raw38309Labels raw38309step0Labels labelEmbedding2 hl
    _ = mixedMoment B node713 node713Labels := by rfl

def raw38310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38310Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw38310step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38310step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38310step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38310step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw38310step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38310 raw38310Labels = mixedMoment B node751 node751Labels := by
  calc
    mixedMoment B raw38310 raw38310Labels = mixedMoment B raw38310step0 raw38310step0Labels := by
      have ha : raw38310step0 = (fun i j => raw38310 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38310step0 raw38310; decide +kernel
      have hl : raw38310step0Labels = raw38310Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38310 raw38310Labels permutation153 permutation7
    mixedMoment B raw38310step0 raw38310step0Labels = mixedMoment B raw38310step1 raw38310step1Labels := by
      have ha : raw38310step1 = -raw38310step0 := by apply Matrix.ext; change ∀ i j, raw38310step1 i j = -(raw38310step0 i j); unfold raw38310step1 raw38310step0; decide +kernel
      have hl : raw38310step1Labels = raw38310step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38310step1 raw38310step1Labels = mixedMoment B raw38310step2 raw38310step2Labels := by
      have ha : raw38310step2 = raw38310step1 := by apply Matrix.ext; unfold raw38310step2 raw38310step1; decide +kernel
      have hl : raw38310step1Labels = labelEmbedding4 ∘ raw38310step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38310step1 raw38310step1Labels raw38310step2Labels labelEmbedding4 hl
    _ = mixedMoment B node751 node751Labels := by rfl

def raw38311 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw38311Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw38311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38311 raw38311Labels = mixedMoment B node715 node715Labels := by
  calc
    mixedMoment B raw38311 raw38311Labels = mixedMoment B raw38311step0 raw38311step0Labels := by
      have ha : raw38311step0 = raw38311 := by apply Matrix.ext; unfold raw38311step0 raw38311; decide +kernel
      have hl : raw38311Labels = labelEmbedding2 ∘ raw38311step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38311 raw38311Labels raw38311step0Labels labelEmbedding2 hl
    _ = mixedMoment B node715 node715Labels := by rfl

def raw38312 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw38312Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, -1, 3]]
def raw38312step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw38312step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38312step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 1, -3]]
def raw38312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38312 raw38312Labels = mixedMoment B node753 node753Labels := by
  calc
    mixedMoment B raw38312 raw38312Labels = mixedMoment B raw38312step0 raw38312step0Labels := by
      have ha : raw38312step0 = (fun i j => raw38312 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38312step0 raw38312; decide +kernel
      have hl : raw38312step0Labels = raw38312Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38312 raw38312Labels permutation32 permutation7
    mixedMoment B raw38312step0 raw38312step0Labels = mixedMoment B raw38312step1 raw38312step1Labels := by
      have ha : raw38312step1 = -raw38312step0 := by apply Matrix.ext; change ∀ i j, raw38312step1 i j = -(raw38312step0 i j); unfold raw38312step1 raw38312step0; decide +kernel
      have hl : raw38312step1Labels = raw38312step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38312step1 raw38312step1Labels = mixedMoment B raw38312step2 raw38312step2Labels := by
      have ha : raw38312step2 = raw38312step1 := by apply Matrix.ext; unfold raw38312step2 raw38312step1; decide +kernel
      have hl : raw38312step1Labels = labelEmbedding4 ∘ raw38312step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38312step1 raw38312step1Labels raw38312step2Labels labelEmbedding4 hl
    _ = mixedMoment B node753 node753Labels := by rfl

def raw38313 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw38313Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw38313step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38313 raw38313Labels = mixedMoment B node716 node716Labels := by
  calc
    mixedMoment B raw38313 raw38313Labels = mixedMoment B raw38313step0 raw38313step0Labels := by
      have ha : raw38313step0 = raw38313 := by apply Matrix.ext; unfold raw38313step0 raw38313; decide +kernel
      have hl : raw38313Labels = labelEmbedding2 ∘ raw38313step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38313 raw38313Labels raw38313step0Labels labelEmbedding2 hl
    _ = mixedMoment B node716 node716Labels := by rfl

def raw38314 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw38314Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 1, 2]]
def raw38314step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw38314step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -1, -2]]
def raw38314step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38314 raw38314Labels = mixedMoment B node752 node752Labels := by
  calc
    mixedMoment B raw38314 raw38314Labels = mixedMoment B raw38314step0 raw38314step0Labels := by
      have ha : raw38314step0 = (fun i j => raw38314 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38314step0 raw38314; decide +kernel
      have hl : raw38314step0Labels = raw38314Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38314 raw38314Labels permutation32 permutation7
    mixedMoment B raw38314step0 raw38314step0Labels = mixedMoment B raw38314step1 raw38314step1Labels := by
      have ha : raw38314step1 = -raw38314step0 := by apply Matrix.ext; change ∀ i j, raw38314step1 i j = -(raw38314step0 i j); unfold raw38314step1 raw38314step0; decide +kernel
      have hl : raw38314step1Labels = raw38314step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38314step1 raw38314step1Labels = mixedMoment B raw38314step2 raw38314step2Labels := by
      have ha : raw38314step2 = raw38314step1 := by apply Matrix.ext; unfold raw38314step2 raw38314step1; decide +kernel
      have hl : raw38314step1Labels = labelEmbedding4 ∘ raw38314step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38314step1 raw38314step1Labels raw38314step2Labels labelEmbedding4 hl
    _ = mixedMoment B node752 node752Labels := by rfl

def raw38315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38315Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38315step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38315 raw38315Labels = mixedMoment B node719 node719Labels := by
  calc
    mixedMoment B raw38315 raw38315Labels = mixedMoment B raw38315step0 raw38315step0Labels := by
      have ha : raw38315step0 = raw38315 := by apply Matrix.ext; unfold raw38315step0 raw38315; decide +kernel
      have hl : raw38315Labels = labelEmbedding2 ∘ raw38315step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38315 raw38315Labels raw38315step0Labels labelEmbedding2 hl
    _ = mixedMoment B node719 node719Labels := by rfl

def raw38316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38316Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw38316step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38316step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38316step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38316step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38316 raw38316Labels = mixedMoment B node756 node756Labels := by
  calc
    mixedMoment B raw38316 raw38316Labels = mixedMoment B raw38316step0 raw38316step0Labels := by
      have ha : raw38316step0 = (fun i j => raw38316 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38316step0 raw38316; decide +kernel
      have hl : raw38316step0Labels = raw38316Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38316 raw38316Labels permutation170 permutation7
    mixedMoment B raw38316step0 raw38316step0Labels = mixedMoment B raw38316step1 raw38316step1Labels := by
      have ha : raw38316step1 = -raw38316step0 := by apply Matrix.ext; change ∀ i j, raw38316step1 i j = -(raw38316step0 i j); unfold raw38316step1 raw38316step0; decide +kernel
      have hl : raw38316step1Labels = raw38316step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38316step1 raw38316step1Labels = mixedMoment B raw38316step2 raw38316step2Labels := by
      have ha : raw38316step2 = raw38316step1 := by apply Matrix.ext; unfold raw38316step2 raw38316step1; decide +kernel
      have hl : raw38316step1Labels = labelEmbedding4 ∘ raw38316step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38316step1 raw38316step1Labels raw38316step2Labels labelEmbedding4 hl
    _ = mixedMoment B node756 node756Labels := by rfl

def raw38317 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38317Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38317 raw38317Labels = mixedMoment B node720 node720Labels := by
  calc
    mixedMoment B raw38317 raw38317Labels = mixedMoment B raw38317step0 raw38317step0Labels := by
      have ha : raw38317step0 = raw38317 := by apply Matrix.ext; unfold raw38317step0 raw38317; decide +kernel
      have hl : raw38317Labels = labelEmbedding2 ∘ raw38317step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38317 raw38317Labels raw38317step0Labels labelEmbedding2 hl
    _ = mixedMoment B node720 node720Labels := by rfl

def raw38318 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38318Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw38318step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw38318step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw38318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38318 raw38318Labels = mixedMoment B node769 node769Labels := by
  calc
    mixedMoment B raw38318 raw38318Labels = mixedMoment B raw38318step0 raw38318step0Labels := by
      have ha : raw38318step0 = (fun i j => raw38318 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38318step0 raw38318; decide +kernel
      have hl : raw38318step0Labels = raw38318Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38318 raw38318Labels permutation33 permutation7
    mixedMoment B raw38318step0 raw38318step0Labels = mixedMoment B raw38318step1 raw38318step1Labels := by
      have ha : raw38318step1 = -raw38318step0 := by apply Matrix.ext; change ∀ i j, raw38318step1 i j = -(raw38318step0 i j); unfold raw38318step1 raw38318step0; decide +kernel
      have hl : raw38318step1Labels = raw38318step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38318step1 raw38318step1Labels = mixedMoment B raw38318step2 raw38318step2Labels := by
      have ha : raw38318step2 = raw38318step1 := by apply Matrix.ext; unfold raw38318step2 raw38318step1; decide +kernel
      have hl : raw38318step1Labels = labelEmbedding4 ∘ raw38318step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38318step1 raw38318step1Labels raw38318step2Labels labelEmbedding4 hl
    _ = mixedMoment B node769 node769Labels := by rfl

def raw38319 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38319Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38319step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38319 raw38319Labels = mixedMoment B node721 node721Labels := by
  calc
    mixedMoment B raw38319 raw38319Labels = mixedMoment B raw38319step0 raw38319step0Labels := by
      have ha : raw38319step0 = raw38319 := by apply Matrix.ext; unfold raw38319step0 raw38319; decide +kernel
      have hl : raw38319Labels = labelEmbedding2 ∘ raw38319step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38319 raw38319Labels raw38319step0Labels labelEmbedding2 hl
    _ = mixedMoment B node721 node721Labels := by rfl

def raw38320 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38320Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 1, 2]]
def raw38320step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def raw38320step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38320step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -1, -2]]
def raw38320step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38320 raw38320Labels = mixedMoment B node757 node757Labels := by
  calc
    mixedMoment B raw38320 raw38320Labels = mixedMoment B raw38320step0 raw38320step0Labels := by
      have ha : raw38320step0 = (fun i j => raw38320 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38320step0 raw38320; decide +kernel
      have hl : raw38320step0Labels = raw38320Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38320 raw38320Labels permutation34 permutation7
    mixedMoment B raw38320step0 raw38320step0Labels = mixedMoment B raw38320step1 raw38320step1Labels := by
      have ha : raw38320step1 = -raw38320step0 := by apply Matrix.ext; change ∀ i j, raw38320step1 i j = -(raw38320step0 i j); unfold raw38320step1 raw38320step0; decide +kernel
      have hl : raw38320step1Labels = raw38320step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38320step1 raw38320step1Labels = mixedMoment B raw38320step2 raw38320step2Labels := by
      have ha : raw38320step2 = raw38320step1 := by apply Matrix.ext; unfold raw38320step2 raw38320step1; decide +kernel
      have hl : raw38320step1Labels = labelEmbedding4 ∘ raw38320step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38320step1 raw38320step1Labels raw38320step2Labels labelEmbedding4 hl
    _ = mixedMoment B node757 node757Labels := by rfl

def raw38321 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38321Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38321step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38321 raw38321Labels = mixedMoment B node724 node724Labels := by
  calc
    mixedMoment B raw38321 raw38321Labels = mixedMoment B raw38321step0 raw38321step0Labels := by
      have ha : raw38321step0 = raw38321 := by apply Matrix.ext; unfold raw38321step0 raw38321; decide +kernel
      have hl : raw38321Labels = labelEmbedding2 ∘ raw38321step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38321 raw38321Labels raw38321step0Labels labelEmbedding2 hl
    _ = mixedMoment B node724 node724Labels := by rfl

def raw38322 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38322Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw38322step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38322step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw38322step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38322step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw38322step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38322 raw38322Labels = mixedMoment B node758 node758Labels := by
  calc
    mixedMoment B raw38322 raw38322Labels = mixedMoment B raw38322step0 raw38322step0Labels := by
      have ha : raw38322step0 = (fun i j => raw38322 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38322step0 raw38322; decide +kernel
      have hl : raw38322step0Labels = raw38322Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38322 raw38322Labels permutation34 permutation7
    mixedMoment B raw38322step0 raw38322step0Labels = mixedMoment B raw38322step1 raw38322step1Labels := by
      have ha : raw38322step1 = -raw38322step0 := by apply Matrix.ext; change ∀ i j, raw38322step1 i j = -(raw38322step0 i j); unfold raw38322step1 raw38322step0; decide +kernel
      have hl : raw38322step1Labels = raw38322step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38322step1 raw38322step1Labels = mixedMoment B raw38322step2 raw38322step2Labels := by
      have ha : raw38322step2 = raw38322step1 := by apply Matrix.ext; unfold raw38322step2 raw38322step1; decide +kernel
      have hl : raw38322step1Labels = labelEmbedding4 ∘ raw38322step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38322step1 raw38322step1Labels raw38322step2Labels labelEmbedding4 hl
    _ = mixedMoment B node758 node758Labels := by rfl

def raw38323 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38323Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38323 raw38323Labels = mixedMoment B node725 node725Labels := by
  calc
    mixedMoment B raw38323 raw38323Labels = mixedMoment B raw38323step0 raw38323step0Labels := by
      have ha : raw38323step0 = raw38323 := by apply Matrix.ext; unfold raw38323step0 raw38323; decide +kernel
      have hl : raw38323Labels = labelEmbedding2 ∘ raw38323step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38323 raw38323Labels raw38323step0Labels labelEmbedding2 hl
    _ = mixedMoment B node725 node725Labels := by rfl

def raw38324 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38324Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw38324step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw38324step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw38324step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38324 raw38324Labels = mixedMoment B node771 node771Labels := by
  calc
    mixedMoment B raw38324 raw38324Labels = mixedMoment B raw38324step0 raw38324step0Labels := by
      have ha : raw38324step0 = (fun i j => raw38324 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38324step0 raw38324; decide +kernel
      have hl : raw38324step0Labels = raw38324Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38324 raw38324Labels permutation35 permutation7
    mixedMoment B raw38324step0 raw38324step0Labels = mixedMoment B raw38324step1 raw38324step1Labels := by
      have ha : raw38324step1 = -raw38324step0 := by apply Matrix.ext; change ∀ i j, raw38324step1 i j = -(raw38324step0 i j); unfold raw38324step1 raw38324step0; decide +kernel
      have hl : raw38324step1Labels = raw38324step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38324step1 raw38324step1Labels = mixedMoment B raw38324step2 raw38324step2Labels := by
      have ha : raw38324step2 = raw38324step1 := by apply Matrix.ext; unfold raw38324step2 raw38324step1; decide +kernel
      have hl : raw38324step1Labels = labelEmbedding4 ∘ raw38324step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38324step1 raw38324step1Labels raw38324step2Labels labelEmbedding4 hl
    _ = mixedMoment B node771 node771Labels := by rfl

def raw38325 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw38325Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38325step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw38325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38325 raw38325Labels = mixedMoment B node726 node726Labels := by
  calc
    mixedMoment B raw38325 raw38325Labels = mixedMoment B raw38325step0 raw38325step0Labels := by
      have ha : raw38325step0 = raw38325 := by apply Matrix.ext; unfold raw38325step0 raw38325; decide +kernel
      have hl : raw38325Labels = labelEmbedding2 ∘ raw38325step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38325 raw38325Labels raw38325step0Labels labelEmbedding2 hl
    _ = mixedMoment B node726 node726Labels := by rfl

def raw38326 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![4, -2, -2]]
def raw38326Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38326step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-2, 1, 1], ![-2, -2, 4]]
def raw38326step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![2, -1, -1], ![2, 2, -4]]
def raw38326step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38326step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![2, -1, -1], ![2, 2, -4]]
def raw38326step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38326 raw38326Labels = mixedMoment B node774 node774Labels := by
  calc
    mixedMoment B raw38326 raw38326Labels = mixedMoment B raw38326step0 raw38326step0Labels := by
      have ha : raw38326step0 = (fun i j => raw38326 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38326step0 raw38326; decide +kernel
      have hl : raw38326step0Labels = raw38326Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38326 raw38326Labels permutation8 permutation7
    mixedMoment B raw38326step0 raw38326step0Labels = mixedMoment B raw38326step1 raw38326step1Labels := by
      have ha : raw38326step1 = -raw38326step0 := by apply Matrix.ext; change ∀ i j, raw38326step1 i j = -(raw38326step0 i j); unfold raw38326step1 raw38326step0; decide +kernel
      have hl : raw38326step1Labels = raw38326step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38326step1 raw38326step1Labels = mixedMoment B raw38326step2 raw38326step2Labels := by
      have ha : raw38326step2 = raw38326step1 := by apply Matrix.ext; unfold raw38326step2 raw38326step1; decide +kernel
      have hl : raw38326step1Labels = labelEmbedding4 ∘ raw38326step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38326step1 raw38326step1Labels raw38326step2Labels labelEmbedding4 hl
    _ = mixedMoment B node774 node774Labels := by rfl

def raw38327 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -2, 0], ![3, 1, -4]]
def raw38327Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38327step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -2, 0], ![3, 1, -4]]
def raw38327step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38327 raw38327Labels = mixedMoment B node727 node727Labels := by
  calc
    mixedMoment B raw38327 raw38327Labels = mixedMoment B raw38327step0 raw38327step0Labels := by
      have ha : raw38327step0 = raw38327 := by apply Matrix.ext; unfold raw38327step0 raw38327; decide +kernel
      have hl : raw38327Labels = labelEmbedding2 ∘ raw38327step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38327 raw38327Labels raw38327step0Labels labelEmbedding2 hl
    _ = mixedMoment B node727 node727Labels := by rfl

def raw38328 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -2, 0], ![3, 1, -4]]
def raw38328Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38328step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![0, -2, 2], ![-4, 1, 3]]
def raw38328step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38328step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![4, -1, -3]]
def raw38328step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38328step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![0, 2, -2], ![4, -1, -3]]
def raw38328step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38328 raw38328Labels = mixedMoment B node759 node759Labels := by
  calc
    mixedMoment B raw38328 raw38328Labels = mixedMoment B raw38328step0 raw38328step0Labels := by
      have ha : raw38328step0 = (fun i j => raw38328 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38328step0 raw38328; decide +kernel
      have hl : raw38328step0Labels = raw38328Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38328 raw38328Labels permutation8 permutation7
    mixedMoment B raw38328step0 raw38328step0Labels = mixedMoment B raw38328step1 raw38328step1Labels := by
      have ha : raw38328step1 = -raw38328step0 := by apply Matrix.ext; change ∀ i j, raw38328step1 i j = -(raw38328step0 i j); unfold raw38328step1 raw38328step0; decide +kernel
      have hl : raw38328step1Labels = raw38328step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38328step1 raw38328step1Labels = mixedMoment B raw38328step2 raw38328step2Labels := by
      have ha : raw38328step2 = raw38328step1 := by apply Matrix.ext; unfold raw38328step2 raw38328step1; decide +kernel
      have hl : raw38328step1Labels = labelEmbedding4 ∘ raw38328step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38328step1 raw38328step1Labels raw38328step2Labels labelEmbedding4 hl
    _ = mixedMoment B node759 node759Labels := by rfl

def raw38329 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw38329Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38329step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw38329step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38329 raw38329Labels = mixedMoment B node729 node729Labels := by
  calc
    mixedMoment B raw38329 raw38329Labels = mixedMoment B raw38329step0 raw38329step0Labels := by
      have ha : raw38329step0 = raw38329 := by apply Matrix.ext; unfold raw38329step0 raw38329; decide +kernel
      have hl : raw38329Labels = labelEmbedding2 ∘ raw38329step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38329 raw38329Labels raw38329step0Labels labelEmbedding2 hl
    _ = mixedMoment B node729 node729Labels := by rfl

def raw38330 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw38330Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38330step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, -2, 3], ![-3, 1, 2]]
def raw38330step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 2, -3], ![3, -1, -2]]
def raw38330step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38330step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 2, -3], ![3, -1, -2]]
def raw38330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38330 raw38330Labels = mixedMoment B node773 node773Labels := by
  calc
    mixedMoment B raw38330 raw38330Labels = mixedMoment B raw38330step0 raw38330step0Labels := by
      have ha : raw38330step0 = (fun i j => raw38330 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38330step0 raw38330; decide +kernel
      have hl : raw38330step0Labels = raw38330Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38330 raw38330Labels permutation9 permutation7
    mixedMoment B raw38330step0 raw38330step0Labels = mixedMoment B raw38330step1 raw38330step1Labels := by
      have ha : raw38330step1 = -raw38330step0 := by apply Matrix.ext; change ∀ i j, raw38330step1 i j = -(raw38330step0 i j); unfold raw38330step1 raw38330step0; decide +kernel
      have hl : raw38330step1Labels = raw38330step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38330step1 raw38330step1Labels = mixedMoment B raw38330step2 raw38330step2Labels := by
      have ha : raw38330step2 = raw38330step1 := by apply Matrix.ext; unfold raw38330step2 raw38330step1; decide +kernel
      have hl : raw38330step1Labels = labelEmbedding4 ∘ raw38330step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38330step1 raw38330step1Labels raw38330step2Labels labelEmbedding4 hl
    _ = mixedMoment B node773 node773Labels := by rfl

def raw38331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38331Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38331 raw38331Labels = mixedMoment B node730 node730Labels := by
  calc
    mixedMoment B raw38331 raw38331Labels = mixedMoment B raw38331step0 raw38331step0Labels := by
      have ha : raw38331step0 = raw38331 := by apply Matrix.ext; unfold raw38331step0 raw38331; decide +kernel
      have hl : raw38331Labels = labelEmbedding2 ∘ raw38331step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38331 raw38331Labels raw38331step0Labels labelEmbedding2 hl
    _ = mixedMoment B node730 node730Labels := by rfl

def raw38332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw38332Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw38332step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38332step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw38332step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38332step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw38332step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38332 raw38332Labels = mixedMoment B node780 node780Labels := by
  calc
    mixedMoment B raw38332 raw38332Labels = mixedMoment B raw38332step0 raw38332step0Labels := by
      have ha : raw38332step0 = (fun i j => raw38332 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38332step0 raw38332; decide +kernel
      have hl : raw38332step0Labels = raw38332Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38332 raw38332Labels permutation182 permutation7
    mixedMoment B raw38332step0 raw38332step0Labels = mixedMoment B raw38332step1 raw38332step1Labels := by
      have ha : raw38332step1 = -raw38332step0 := by apply Matrix.ext; change ∀ i j, raw38332step1 i j = -(raw38332step0 i j); unfold raw38332step1 raw38332step0; decide +kernel
      have hl : raw38332step1Labels = raw38332step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38332step1 raw38332step1Labels = mixedMoment B raw38332step2 raw38332step2Labels := by
      have ha : raw38332step2 = raw38332step1 := by apply Matrix.ext; unfold raw38332step2 raw38332step1; decide +kernel
      have hl : raw38332step1Labels = labelEmbedding4 ∘ raw38332step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38332step1 raw38332step1Labels raw38332step2Labels labelEmbedding4 hl
    _ = mixedMoment B node780 node780Labels := by rfl

def raw38333 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38333Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38333step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38333 raw38333Labels = mixedMoment B node731 node731Labels := by
  calc
    mixedMoment B raw38333 raw38333Labels = mixedMoment B raw38333step0 raw38333step0Labels := by
      have ha : raw38333step0 = raw38333 := by apply Matrix.ext; unfold raw38333step0 raw38333; decide +kernel
      have hl : raw38333Labels = labelEmbedding2 ∘ raw38333step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38333 raw38333Labels raw38333step0Labels labelEmbedding2 hl
    _ = mixedMoment B node731 node731Labels := by rfl

def raw38334 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38334Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw38334step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38334step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw38334step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38334step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw38334step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38334 raw38334Labels = mixedMoment B node781 node781Labels := by
  calc
    mixedMoment B raw38334 raw38334Labels = mixedMoment B raw38334step0 raw38334step0Labels := by
      have ha : raw38334step0 = (fun i j => raw38334 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38334step0 raw38334; decide +kernel
      have hl : raw38334step0Labels = raw38334Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38334 raw38334Labels permutation40 permutation7
    mixedMoment B raw38334step0 raw38334step0Labels = mixedMoment B raw38334step1 raw38334step1Labels := by
      have ha : raw38334step1 = -raw38334step0 := by apply Matrix.ext; change ∀ i j, raw38334step1 i j = -(raw38334step0 i j); unfold raw38334step1 raw38334step0; decide +kernel
      have hl : raw38334step1Labels = raw38334step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38334step1 raw38334step1Labels = mixedMoment B raw38334step2 raw38334step2Labels := by
      have ha : raw38334step2 = raw38334step1 := by apply Matrix.ext; unfold raw38334step2 raw38334step1; decide +kernel
      have hl : raw38334step1Labels = labelEmbedding4 ∘ raw38334step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38334step1 raw38334step1Labels raw38334step2Labels labelEmbedding4 hl
    _ = mixedMoment B node781 node781Labels := by rfl

def raw38335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38335Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38335 raw38335Labels = mixedMoment B node732 node732Labels := by
  calc
    mixedMoment B raw38335 raw38335Labels = mixedMoment B raw38335step0 raw38335step0Labels := by
      have ha : raw38335step0 = raw38335 := by apply Matrix.ext; unfold raw38335step0 raw38335; decide +kernel
      have hl : raw38335Labels = labelEmbedding2 ∘ raw38335step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38335 raw38335Labels raw38335step0Labels labelEmbedding2 hl
    _ = mixedMoment B node732 node732Labels := by rfl

def raw38336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw38336Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw38336step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38336step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38336step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38336step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw38336step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38336 raw38336Labels = mixedMoment B node798 node798Labels := by
  calc
    mixedMoment B raw38336 raw38336Labels = mixedMoment B raw38336step0 raw38336step0Labels := by
      have ha : raw38336step0 = (fun i j => raw38336 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38336step0 raw38336; decide +kernel
      have hl : raw38336step0Labels = raw38336Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38336 raw38336Labels permutation176 permutation7
    mixedMoment B raw38336step0 raw38336step0Labels = mixedMoment B raw38336step1 raw38336step1Labels := by
      have ha : raw38336step1 = -raw38336step0 := by apply Matrix.ext; change ∀ i j, raw38336step1 i j = -(raw38336step0 i j); unfold raw38336step1 raw38336step0; decide +kernel
      have hl : raw38336step1Labels = raw38336step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38336step1 raw38336step1Labels = mixedMoment B raw38336step2 raw38336step2Labels := by
      have ha : raw38336step2 = raw38336step1 := by apply Matrix.ext; unfold raw38336step2 raw38336step1; decide +kernel
      have hl : raw38336step1Labels = labelEmbedding4 ∘ raw38336step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38336step1 raw38336step1Labels raw38336step2Labels labelEmbedding4 hl
    _ = mixedMoment B node798 node798Labels := by rfl

def raw38337 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38337Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38337 raw38337Labels = mixedMoment B node733 node733Labels := by
  calc
    mixedMoment B raw38337 raw38337Labels = mixedMoment B raw38337step0 raw38337step0Labels := by
      have ha : raw38337step0 = raw38337 := by apply Matrix.ext; unfold raw38337step0 raw38337; decide +kernel
      have hl : raw38337Labels = labelEmbedding2 ∘ raw38337step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38337 raw38337Labels raw38337step0Labels labelEmbedding2 hl
    _ = mixedMoment B node733 node733Labels := by rfl

def raw38338 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38338Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw38338step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw38338step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38338step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw38338step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38338 raw38338Labels = mixedMoment B node799 node799Labels := by
  calc
    mixedMoment B raw38338 raw38338Labels = mixedMoment B raw38338step0 raw38338step0Labels := by
      have ha : raw38338step0 = (fun i j => raw38338 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38338step0 raw38338; decide +kernel
      have hl : raw38338step0Labels = raw38338Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38338 raw38338Labels permutation38 permutation7
    mixedMoment B raw38338step0 raw38338step0Labels = mixedMoment B raw38338step1 raw38338step1Labels := by
      have ha : raw38338step1 = -raw38338step0 := by apply Matrix.ext; change ∀ i j, raw38338step1 i j = -(raw38338step0 i j); unfold raw38338step1 raw38338step0; decide +kernel
      have hl : raw38338step1Labels = raw38338step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38338step1 raw38338step1Labels = mixedMoment B raw38338step2 raw38338step2Labels := by
      have ha : raw38338step2 = raw38338step1 := by apply Matrix.ext; unfold raw38338step2 raw38338step1; decide +kernel
      have hl : raw38338step1Labels = labelEmbedding4 ∘ raw38338step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38338step1 raw38338step1Labels raw38338step2Labels labelEmbedding4 hl
    _ = mixedMoment B node799 node799Labels := by rfl

def raw38339 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38339Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38339 raw38339Labels = mixedMoment B node734 node734Labels := by
  calc
    mixedMoment B raw38339 raw38339Labels = mixedMoment B raw38339step0 raw38339step0Labels := by
      have ha : raw38339step0 = raw38339 := by apply Matrix.ext; unfold raw38339step0 raw38339; decide +kernel
      have hl : raw38339Labels = labelEmbedding2 ∘ raw38339step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38339 raw38339Labels raw38339step0Labels labelEmbedding2 hl
    _ = mixedMoment B node734 node734Labels := by rfl

def raw38340 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38340Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw38340step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw38340step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38340step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw38340step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38340 raw38340Labels = mixedMoment B node800 node800Labels := by
  calc
    mixedMoment B raw38340 raw38340Labels = mixedMoment B raw38340step0 raw38340step0Labels := by
      have ha : raw38340step0 = (fun i j => raw38340 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38340step0 raw38340; decide +kernel
      have hl : raw38340step0Labels = raw38340Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38340 raw38340Labels permutation38 permutation7
    mixedMoment B raw38340step0 raw38340step0Labels = mixedMoment B raw38340step1 raw38340step1Labels := by
      have ha : raw38340step1 = -raw38340step0 := by apply Matrix.ext; change ∀ i j, raw38340step1 i j = -(raw38340step0 i j); unfold raw38340step1 raw38340step0; decide +kernel
      have hl : raw38340step1Labels = raw38340step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38340step1 raw38340step1Labels = mixedMoment B raw38340step2 raw38340step2Labels := by
      have ha : raw38340step2 = raw38340step1 := by apply Matrix.ext; unfold raw38340step2 raw38340step1; decide +kernel
      have hl : raw38340step1Labels = labelEmbedding4 ∘ raw38340step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38340step1 raw38340step1Labels raw38340step2Labels labelEmbedding4 hl
    _ = mixedMoment B node800 node800Labels := by rfl

def raw38341 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw38341Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38341step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw38341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38341 raw38341Labels = mixedMoment B node735 node735Labels := by
  calc
    mixedMoment B raw38341 raw38341Labels = mixedMoment B raw38341step0 raw38341step0Labels := by
      have ha : raw38341step0 = raw38341 := by apply Matrix.ext; unfold raw38341step0 raw38341; decide +kernel
      have hl : raw38341Labels = labelEmbedding2 ∘ raw38341step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38341 raw38341Labels raw38341step0Labels labelEmbedding2 hl
    _ = mixedMoment B node735 node735Labels := by rfl

def raw38342 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![4, -1, -3]]
def raw38342Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38342step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-3, -1, 4]]
def raw38342step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38342step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![3, 1, -4]]
def raw38342step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38342step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![3, 1, -4]]
def raw38342step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38342 raw38342Labels = mixedMoment B node801 node801Labels := by
  calc
    mixedMoment B raw38342 raw38342Labels = mixedMoment B raw38342step0 raw38342step0Labels := by
      have ha : raw38342step0 = (fun i j => raw38342 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38342step0 raw38342; decide +kernel
      have hl : raw38342step0Labels = raw38342Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38342 raw38342Labels permutation10 permutation7
    mixedMoment B raw38342step0 raw38342step0Labels = mixedMoment B raw38342step1 raw38342step1Labels := by
      have ha : raw38342step1 = -raw38342step0 := by apply Matrix.ext; change ∀ i j, raw38342step1 i j = -(raw38342step0 i j); unfold raw38342step1 raw38342step0; decide +kernel
      have hl : raw38342step1Labels = raw38342step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38342step1 raw38342step1Labels = mixedMoment B raw38342step2 raw38342step2Labels := by
      have ha : raw38342step2 = raw38342step1 := by apply Matrix.ext; unfold raw38342step2 raw38342step1; decide +kernel
      have hl : raw38342step1Labels = labelEmbedding4 ∘ raw38342step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38342step1 raw38342step1Labels raw38342step2Labels labelEmbedding4 hl
    _ = mixedMoment B node801 node801Labels := by rfl

def raw38343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38343Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38343step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38343 raw38343Labels = mixedMoment B node736 node736Labels := by
  calc
    mixedMoment B raw38343 raw38343Labels = mixedMoment B raw38343step0 raw38343step0Labels := by
      have ha : raw38343step0 = raw38343 := by apply Matrix.ext; unfold raw38343step0 raw38343; decide +kernel
      have hl : raw38343Labels = labelEmbedding2 ∘ raw38343step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38343 raw38343Labels raw38343step0Labels labelEmbedding2 hl
    _ = mixedMoment B node736 node736Labels := by rfl

def raw38344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38344Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38344step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw38344step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38344step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38344step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38344step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw38344step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38344 raw38344Labels = mixedMoment B node818 node818Labels := by
  calc
    mixedMoment B raw38344 raw38344Labels = mixedMoment B raw38344step0 raw38344step0Labels := by
      have ha : raw38344step0 = (fun i j => raw38344 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38344step0 raw38344; decide +kernel
      have hl : raw38344step0Labels = raw38344Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38344 raw38344Labels permutation246 permutation7
    mixedMoment B raw38344step0 raw38344step0Labels = mixedMoment B raw38344step1 raw38344step1Labels := by
      have ha : raw38344step1 = -raw38344step0 := by apply Matrix.ext; change ∀ i j, raw38344step1 i j = -(raw38344step0 i j); unfold raw38344step1 raw38344step0; decide +kernel
      have hl : raw38344step1Labels = raw38344step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38344step1 raw38344step1Labels = mixedMoment B raw38344step2 raw38344step2Labels := by
      have ha : raw38344step2 = raw38344step1 := by apply Matrix.ext; unfold raw38344step2 raw38344step1; decide +kernel
      have hl : raw38344step1Labels = labelEmbedding4 ∘ raw38344step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38344step1 raw38344step1Labels raw38344step2Labels labelEmbedding4 hl
    _ = mixedMoment B node818 node818Labels := by rfl

def raw38345 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38345Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38345 raw38345Labels = mixedMoment B node737 node737Labels := by
  calc
    mixedMoment B raw38345 raw38345Labels = mixedMoment B raw38345step0 raw38345step0Labels := by
      have ha : raw38345step0 = raw38345 := by apply Matrix.ext; unfold raw38345step0 raw38345; decide +kernel
      have hl : raw38345Labels = labelEmbedding2 ∘ raw38345step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38345 raw38345Labels raw38345step0Labels labelEmbedding2 hl
    _ = mixedMoment B node737 node737Labels := by rfl

def raw38346 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38346Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw38346step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38346step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38346step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw38346step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38346 raw38346Labels = mixedMoment B node840 node840Labels := by
  calc
    mixedMoment B raw38346 raw38346Labels = mixedMoment B raw38346step0 raw38346step0Labels := by
      have ha : raw38346step0 = (fun i j => raw38346 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38346step0 raw38346; decide +kernel
      have hl : raw38346step0Labels = raw38346Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38346 raw38346Labels permutation32 permutation7
    mixedMoment B raw38346step0 raw38346step0Labels = mixedMoment B raw38346step1 raw38346step1Labels := by
      have ha : raw38346step1 = -raw38346step0 := by apply Matrix.ext; change ∀ i j, raw38346step1 i j = -(raw38346step0 i j); unfold raw38346step1 raw38346step0; decide +kernel
      have hl : raw38346step1Labels = raw38346step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38346step1 raw38346step1Labels = mixedMoment B raw38346step2 raw38346step2Labels := by
      have ha : raw38346step2 = raw38346step1 := by apply Matrix.ext; unfold raw38346step2 raw38346step1; decide +kernel
      have hl : raw38346step1Labels = labelEmbedding4 ∘ raw38346step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38346step1 raw38346step1Labels raw38346step2Labels labelEmbedding4 hl
    _ = mixedMoment B node840 node840Labels := by rfl

def raw38347 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38347Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38347 raw38347Labels = mixedMoment B node738 node738Labels := by
  calc
    mixedMoment B raw38347 raw38347Labels = mixedMoment B raw38347step0 raw38347step0Labels := by
      have ha : raw38347step0 = raw38347 := by apply Matrix.ext; unfold raw38347step0 raw38347; decide +kernel
      have hl : raw38347Labels = labelEmbedding2 ∘ raw38347step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38347 raw38347Labels raw38347step0Labels labelEmbedding2 hl
    _ = mixedMoment B node738 node738Labels := by rfl

def raw38348 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38348Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw38348step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw38348step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38348step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw38348step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38348 raw38348Labels = mixedMoment B node819 node819Labels := by
  calc
    mixedMoment B raw38348 raw38348Labels = mixedMoment B raw38348step0 raw38348step0Labels := by
      have ha : raw38348step0 = (fun i j => raw38348 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38348step0 raw38348; decide +kernel
      have hl : raw38348step0Labels = raw38348Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38348 raw38348Labels permutation44 permutation7
    mixedMoment B raw38348step0 raw38348step0Labels = mixedMoment B raw38348step1 raw38348step1Labels := by
      have ha : raw38348step1 = -raw38348step0 := by apply Matrix.ext; change ∀ i j, raw38348step1 i j = -(raw38348step0 i j); unfold raw38348step1 raw38348step0; decide +kernel
      have hl : raw38348step1Labels = raw38348step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38348step1 raw38348step1Labels = mixedMoment B raw38348step2 raw38348step2Labels := by
      have ha : raw38348step2 = raw38348step1 := by apply Matrix.ext; unfold raw38348step2 raw38348step1; decide +kernel
      have hl : raw38348step1Labels = labelEmbedding4 ∘ raw38348step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38348step1 raw38348step1Labels raw38348step2Labels labelEmbedding4 hl
    _ = mixedMoment B node819 node819Labels := by rfl

def raw38349 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38349Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38349step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38349 raw38349Labels = mixedMoment B node739 node739Labels := by
  calc
    mixedMoment B raw38349 raw38349Labels = mixedMoment B raw38349step0 raw38349step0Labels := by
      have ha : raw38349step0 = raw38349 := by apply Matrix.ext; unfold raw38349step0 raw38349; decide +kernel
      have hl : raw38349Labels = labelEmbedding2 ∘ raw38349step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38349 raw38349Labels raw38349step0Labels labelEmbedding2 hl
    _ = mixedMoment B node739 node739Labels := by rfl

def raw38350 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38350Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw38350step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38350step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw38350step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38350 raw38350Labels = mixedMoment B node841 node841Labels := by
  calc
    mixedMoment B raw38350 raw38350Labels = mixedMoment B raw38350step0 raw38350step0Labels := by
      have ha : raw38350step0 = (fun i j => raw38350 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38350step0 raw38350; decide +kernel
      have hl : raw38350step0Labels = raw38350Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38350 raw38350Labels permutation32 permutation7
    mixedMoment B raw38350step0 raw38350step0Labels = mixedMoment B raw38350step1 raw38350step1Labels := by
      have ha : raw38350step1 = -raw38350step0 := by apply Matrix.ext; change ∀ i j, raw38350step1 i j = -(raw38350step0 i j); unfold raw38350step1 raw38350step0; decide +kernel
      have hl : raw38350step1Labels = raw38350step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38350step1 raw38350step1Labels = mixedMoment B raw38350step2 raw38350step2Labels := by
      have ha : raw38350step2 = raw38350step1 := by apply Matrix.ext; unfold raw38350step2 raw38350step1; decide +kernel
      have hl : raw38350step1Labels = labelEmbedding4 ∘ raw38350step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38350step1 raw38350step1Labels raw38350step2Labels labelEmbedding4 hl
    _ = mixedMoment B node841 node841Labels := by rfl

def raw38351 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw38351Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38351step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw38351step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38351 raw38351Labels = mixedMoment B node740 node740Labels := by
  calc
    mixedMoment B raw38351 raw38351Labels = mixedMoment B raw38351step0 raw38351step0Labels := by
      have ha : raw38351step0 = raw38351 := by apply Matrix.ext; unfold raw38351step0 raw38351; decide +kernel
      have hl : raw38351Labels = labelEmbedding2 ∘ raw38351step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38351 raw38351Labels raw38351step0Labels labelEmbedding2 hl
    _ = mixedMoment B node740 node740Labels := by rfl

def raw38352 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![4, -2, -2]]
def raw38352Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38352step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, 0, 1], ![-2, -2, 4]]
def raw38352step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38352step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![2, 2, -4]]
def raw38352step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38352step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![2, 2, -4]]
def raw38352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38352 raw38352Labels = mixedMoment B node842 node842Labels := by
  calc
    mixedMoment B raw38352 raw38352Labels = mixedMoment B raw38352step0 raw38352step0Labels := by
      have ha : raw38352step0 = (fun i j => raw38352 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38352step0 raw38352; decide +kernel
      have hl : raw38352step0Labels = raw38352Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38352 raw38352Labels permutation8 permutation7
    mixedMoment B raw38352step0 raw38352step0Labels = mixedMoment B raw38352step1 raw38352step1Labels := by
      have ha : raw38352step1 = -raw38352step0 := by apply Matrix.ext; change ∀ i j, raw38352step1 i j = -(raw38352step0 i j); unfold raw38352step1 raw38352step0; decide +kernel
      have hl : raw38352step1Labels = raw38352step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38352step1 raw38352step1Labels = mixedMoment B raw38352step2 raw38352step2Labels := by
      have ha : raw38352step2 = raw38352step1 := by apply Matrix.ext; unfold raw38352step2 raw38352step1; decide +kernel
      have hl : raw38352step1Labels = labelEmbedding4 ∘ raw38352step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38352step1 raw38352step1Labels raw38352step2Labels labelEmbedding4 hl
    _ = mixedMoment B node842 node842Labels := by rfl

def raw38353 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -2, 0], ![3, 0, -3]]
def raw38353Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38353step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -2, 0], ![3, 0, -3]]
def raw38353step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38353 raw38353Labels = mixedMoment B node741 node741Labels := by
  calc
    mixedMoment B raw38353 raw38353Labels = mixedMoment B raw38353step0 raw38353step0Labels := by
      have ha : raw38353step0 = raw38353 := by apply Matrix.ext; unfold raw38353step0 raw38353; decide +kernel
      have hl : raw38353Labels = labelEmbedding2 ∘ raw38353step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38353 raw38353Labels raw38353step0Labels labelEmbedding2 hl
    _ = mixedMoment B node741 node741Labels := by rfl

def raw38354 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -2, 0], ![3, 0, -3]]
def raw38354Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38354step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 2, -1], ![-3, 0, 3]]
def raw38354step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![3, 0, -3]]
def raw38354step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38354step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -2, 1], ![3, 0, -3]]
def raw38354step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38354 raw38354Labels = mixedMoment B node820 node820Labels := by
  calc
    mixedMoment B raw38354 raw38354Labels = mixedMoment B raw38354step0 raw38354step0Labels := by
      have ha : raw38354step0 = (fun i j => raw38354 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38354step0 raw38354; decide +kernel
      have hl : raw38354step0Labels = raw38354Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38354 raw38354Labels permutation10 permutation7
    mixedMoment B raw38354step0 raw38354step0Labels = mixedMoment B raw38354step1 raw38354step1Labels := by
      have ha : raw38354step1 = -raw38354step0 := by apply Matrix.ext; change ∀ i j, raw38354step1 i j = -(raw38354step0 i j); unfold raw38354step1 raw38354step0; decide +kernel
      have hl : raw38354step1Labels = raw38354step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38354step1 raw38354step1Labels = mixedMoment B raw38354step2 raw38354step2Labels := by
      have ha : raw38354step2 = raw38354step1 := by apply Matrix.ext; unfold raw38354step2 raw38354step1; decide +kernel
      have hl : raw38354step1Labels = labelEmbedding4 ∘ raw38354step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38354step1 raw38354step1Labels raw38354step2Labels labelEmbedding4 hl
    _ = mixedMoment B node820 node820Labels := by rfl

def raw38355 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38355Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38355step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38355step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38355 raw38355Labels = mixedMoment B node742 node742Labels := by
  calc
    mixedMoment B raw38355 raw38355Labels = mixedMoment B raw38355step0 raw38355step0Labels := by
      have ha : raw38355step0 = raw38355 := by apply Matrix.ext; unfold raw38355step0 raw38355; decide +kernel
      have hl : raw38355Labels = labelEmbedding2 ∘ raw38355step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38355 raw38355Labels raw38355step0Labels labelEmbedding2 hl
    _ = mixedMoment B node742 node742Labels := by rfl

def raw38356 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw38356Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38356step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw38356step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38356step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw38356step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38356step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 1, -2], ![2, 1, -3]]
def raw38356step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38356 raw38356Labels = mixedMoment B node843 node843Labels := by
  calc
    mixedMoment B raw38356 raw38356Labels = mixedMoment B raw38356step0 raw38356step0Labels := by
      have ha : raw38356step0 = (fun i j => raw38356 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38356step0 raw38356; decide +kernel
      have hl : raw38356step0Labels = raw38356Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38356 raw38356Labels permutation8 permutation7
    mixedMoment B raw38356step0 raw38356step0Labels = mixedMoment B raw38356step1 raw38356step1Labels := by
      have ha : raw38356step1 = -raw38356step0 := by apply Matrix.ext; change ∀ i j, raw38356step1 i j = -(raw38356step0 i j); unfold raw38356step1 raw38356step0; decide +kernel
      have hl : raw38356step1Labels = raw38356step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38356step1 raw38356step1Labels = mixedMoment B raw38356step2 raw38356step2Labels := by
      have ha : raw38356step2 = raw38356step1 := by apply Matrix.ext; unfold raw38356step2 raw38356step1; decide +kernel
      have hl : raw38356step1Labels = labelEmbedding4 ∘ raw38356step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38356step1 raw38356step1Labels raw38356step2Labels labelEmbedding4 hl
    _ = mixedMoment B node843 node843Labels := by rfl

def raw38357 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38357Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38357step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38357step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38357 raw38357Labels = mixedMoment B node743 node743Labels := by
  calc
    mixedMoment B raw38357 raw38357Labels = mixedMoment B raw38357step0 raw38357step0Labels := by
      have ha : raw38357step0 = raw38357 := by apply Matrix.ext; unfold raw38357step0 raw38357; decide +kernel
      have hl : raw38357Labels = labelEmbedding2 ∘ raw38357step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38357 raw38357Labels raw38357step0Labels labelEmbedding2 hl
    _ = mixedMoment B node743 node743Labels := by rfl

def raw38358 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw38358Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38358step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw38358step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38358step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def raw38358step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38358step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 2, -3], ![2, 0, -2]]
def raw38358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38358 raw38358Labels = mixedMoment B node844 node844Labels := by
  calc
    mixedMoment B raw38358 raw38358Labels = mixedMoment B raw38358step0 raw38358step0Labels := by
      have ha : raw38358step0 = (fun i j => raw38358 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38358step0 raw38358; decide +kernel
      have hl : raw38358step0Labels = raw38358Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38358 raw38358Labels permutation9 permutation7
    mixedMoment B raw38358step0 raw38358step0Labels = mixedMoment B raw38358step1 raw38358step1Labels := by
      have ha : raw38358step1 = -raw38358step0 := by apply Matrix.ext; change ∀ i j, raw38358step1 i j = -(raw38358step0 i j); unfold raw38358step1 raw38358step0; decide +kernel
      have hl : raw38358step1Labels = raw38358step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38358step1 raw38358step1Labels = mixedMoment B raw38358step2 raw38358step2Labels := by
      have ha : raw38358step2 = raw38358step1 := by apply Matrix.ext; unfold raw38358step2 raw38358step1; decide +kernel
      have hl : raw38358step1Labels = labelEmbedding4 ∘ raw38358step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38358step1 raw38358step1Labels raw38358step2Labels labelEmbedding4 hl
    _ = mixedMoment B node844 node844Labels := by rfl

def raw38359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38359Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38359 raw38359Labels = mixedMoment B node782 node782Labels := by
  calc
    mixedMoment B raw38359 raw38359Labels = mixedMoment B raw38359step0 raw38359step0Labels := by
      have ha : raw38359step0 = raw38359 := by apply Matrix.ext; unfold raw38359step0 raw38359; decide +kernel
      have hl : raw38359Labels = labelEmbedding2 ∘ raw38359step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38359 raw38359Labels raw38359step0Labels labelEmbedding2 hl
    _ = mixedMoment B node782 node782Labels := by rfl

def raw38360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38360Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw38360step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38360step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38360step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38360step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38360step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38360 raw38360Labels = mixedMoment B node782 node782Labels := by
  calc
    mixedMoment B raw38360 raw38360Labels = mixedMoment B raw38360step0 raw38360step0Labels := by
      have ha : raw38360step0 = (fun i j => raw38360 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38360step0 raw38360; decide +kernel
      have hl : raw38360step0Labels = raw38360Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38360 raw38360Labels permutation212 permutation7
    mixedMoment B raw38360step0 raw38360step0Labels = mixedMoment B raw38360step1 raw38360step1Labels := by
      have ha : raw38360step1 = -raw38360step0 := by apply Matrix.ext; change ∀ i j, raw38360step1 i j = -(raw38360step0 i j); unfold raw38360step1 raw38360step0; decide +kernel
      have hl : raw38360step1Labels = raw38360step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38360step1 raw38360step1Labels = mixedMoment B raw38360step2 raw38360step2Labels := by
      have ha : raw38360step2 = raw38360step1 := by apply Matrix.ext; unfold raw38360step2 raw38360step1; decide +kernel
      have hl : raw38360step1Labels = labelEmbedding4 ∘ raw38360step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38360step1 raw38360step1Labels raw38360step2Labels labelEmbedding4 hl
    _ = mixedMoment B node782 node782Labels := by rfl

def raw38361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38361Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38361 raw38361Labels = mixedMoment B node783 node783Labels := by
  calc
    mixedMoment B raw38361 raw38361Labels = mixedMoment B raw38361step0 raw38361step0Labels := by
      have ha : raw38361step0 = raw38361 := by apply Matrix.ext; unfold raw38361step0 raw38361; decide +kernel
      have hl : raw38361Labels = labelEmbedding2 ∘ raw38361step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38361 raw38361Labels raw38361step0Labels labelEmbedding2 hl
    _ = mixedMoment B node783 node783Labels := by rfl

def raw38362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38362Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw38362step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38362step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw38362step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38362step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw38362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38362 raw38362Labels = mixedMoment B node803 node803Labels := by
  calc
    mixedMoment B raw38362 raw38362Labels = mixedMoment B raw38362step0 raw38362step0Labels := by
      have ha : raw38362step0 = (fun i j => raw38362 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38362step0 raw38362; decide +kernel
      have hl : raw38362step0Labels = raw38362Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38362 raw38362Labels permutation200 permutation7
    mixedMoment B raw38362step0 raw38362step0Labels = mixedMoment B raw38362step1 raw38362step1Labels := by
      have ha : raw38362step1 = -raw38362step0 := by apply Matrix.ext; change ∀ i j, raw38362step1 i j = -(raw38362step0 i j); unfold raw38362step1 raw38362step0; decide +kernel
      have hl : raw38362step1Labels = raw38362step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38362step1 raw38362step1Labels = mixedMoment B raw38362step2 raw38362step2Labels := by
      have ha : raw38362step2 = raw38362step1 := by apply Matrix.ext; unfold raw38362step2 raw38362step1; decide +kernel
      have hl : raw38362step1Labels = labelEmbedding4 ∘ raw38362step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38362step1 raw38362step1Labels raw38362step2Labels labelEmbedding4 hl
    _ = mixedMoment B node803 node803Labels := by rfl

def raw38363 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw38363Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw38363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38363 raw38363Labels = mixedMoment B node785 node785Labels := by
  calc
    mixedMoment B raw38363 raw38363Labels = mixedMoment B raw38363step0 raw38363step0Labels := by
      have ha : raw38363step0 = raw38363 := by apply Matrix.ext; unfold raw38363step0 raw38363; decide +kernel
      have hl : raw38363Labels = labelEmbedding2 ∘ raw38363step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38363 raw38363Labels raw38363step0Labels labelEmbedding2 hl
    _ = mixedMoment B node785 node785Labels := by rfl

def raw38364 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw38364Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw38364step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw38364step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38364step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw38364step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38364 raw38364Labels = mixedMoment B node804 node804Labels := by
  calc
    mixedMoment B raw38364 raw38364Labels = mixedMoment B raw38364step0 raw38364step0Labels := by
      have ha : raw38364step0 = (fun i j => raw38364 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38364step0 raw38364; decide +kernel
      have hl : raw38364step0Labels = raw38364Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38364 raw38364Labels permutation44 permutation7
    mixedMoment B raw38364step0 raw38364step0Labels = mixedMoment B raw38364step1 raw38364step1Labels := by
      have ha : raw38364step1 = -raw38364step0 := by apply Matrix.ext; change ∀ i j, raw38364step1 i j = -(raw38364step0 i j); unfold raw38364step1 raw38364step0; decide +kernel
      have hl : raw38364step1Labels = raw38364step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38364step1 raw38364step1Labels = mixedMoment B raw38364step2 raw38364step2Labels := by
      have ha : raw38364step2 = raw38364step1 := by apply Matrix.ext; unfold raw38364step2 raw38364step1; decide +kernel
      have hl : raw38364step1Labels = labelEmbedding4 ∘ raw38364step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38364step1 raw38364step1Labels raw38364step2Labels labelEmbedding4 hl
    _ = mixedMoment B node804 node804Labels := by rfl

def raw38365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38365Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38365step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38365step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38365 raw38365Labels = mixedMoment B node786 node786Labels := by
  calc
    mixedMoment B raw38365 raw38365Labels = mixedMoment B raw38365step0 raw38365step0Labels := by
      have ha : raw38365step0 = raw38365 := by apply Matrix.ext; unfold raw38365step0 raw38365; decide +kernel
      have hl : raw38365Labels = labelEmbedding2 ∘ raw38365step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38365 raw38365Labels raw38365step0Labels labelEmbedding2 hl
    _ = mixedMoment B node786 node786Labels := by rfl

def raw38366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38366Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38366step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw38366step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38366step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38366step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38366step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw38366step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38366 raw38366Labels = mixedMoment B node822 node822Labels := by
  calc
    mixedMoment B raw38366 raw38366Labels = mixedMoment B raw38366step0 raw38366step0Labels := by
      have ha : raw38366step0 = (fun i j => raw38366 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38366step0 raw38366; decide +kernel
      have hl : raw38366step0Labels = raw38366Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38366 raw38366Labels permutation246 permutation7
    mixedMoment B raw38366step0 raw38366step0Labels = mixedMoment B raw38366step1 raw38366step1Labels := by
      have ha : raw38366step1 = -raw38366step0 := by apply Matrix.ext; change ∀ i j, raw38366step1 i j = -(raw38366step0 i j); unfold raw38366step1 raw38366step0; decide +kernel
      have hl : raw38366step1Labels = raw38366step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38366step1 raw38366step1Labels = mixedMoment B raw38366step2 raw38366step2Labels := by
      have ha : raw38366step2 = raw38366step1 := by apply Matrix.ext; unfold raw38366step2 raw38366step1; decide +kernel
      have hl : raw38366step1Labels = labelEmbedding4 ∘ raw38366step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38366step1 raw38366step1Labels raw38366step2Labels labelEmbedding4 hl
    _ = mixedMoment B node822 node822Labels := by rfl

def raw38367 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38367Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38367 raw38367Labels = mixedMoment B node787 node787Labels := by
  calc
    mixedMoment B raw38367 raw38367Labels = mixedMoment B raw38367step0 raw38367step0Labels := by
      have ha : raw38367step0 = raw38367 := by apply Matrix.ext; unfold raw38367step0 raw38367; decide +kernel
      have hl : raw38367Labels = labelEmbedding2 ∘ raw38367step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38367 raw38367Labels raw38367step0Labels labelEmbedding2 hl
    _ = mixedMoment B node787 node787Labels := by rfl

def raw38368 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw38368Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw38368step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw38368step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38368step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw38368step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38368 raw38368Labels = mixedMoment B node847 node847Labels := by
  calc
    mixedMoment B raw38368 raw38368Labels = mixedMoment B raw38368step0 raw38368step0Labels := by
      have ha : raw38368step0 = (fun i j => raw38368 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38368step0 raw38368; decide +kernel
      have hl : raw38368step0Labels = raw38368Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38368 raw38368Labels permutation32 permutation7
    mixedMoment B raw38368step0 raw38368step0Labels = mixedMoment B raw38368step1 raw38368step1Labels := by
      have ha : raw38368step1 = -raw38368step0 := by apply Matrix.ext; change ∀ i j, raw38368step1 i j = -(raw38368step0 i j); unfold raw38368step1 raw38368step0; decide +kernel
      have hl : raw38368step1Labels = raw38368step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38368step1 raw38368step1Labels = mixedMoment B raw38368step2 raw38368step2Labels := by
      have ha : raw38368step2 = raw38368step1 := by apply Matrix.ext; unfold raw38368step2 raw38368step1; decide +kernel
      have hl : raw38368step1Labels = labelEmbedding4 ∘ raw38368step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38368step1 raw38368step1Labels raw38368step2Labels labelEmbedding4 hl
    _ = mixedMoment B node847 node847Labels := by rfl

def raw38369 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38369Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38369 raw38369Labels = mixedMoment B node789 node789Labels := by
  calc
    mixedMoment B raw38369 raw38369Labels = mixedMoment B raw38369step0 raw38369step0Labels := by
      have ha : raw38369step0 = raw38369 := by apply Matrix.ext; unfold raw38369step0 raw38369; decide +kernel
      have hl : raw38369Labels = labelEmbedding2 ∘ raw38369step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38369 raw38369Labels raw38369step0Labels labelEmbedding2 hl
    _ = mixedMoment B node789 node789Labels := by rfl

def raw38370 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw38370Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw38370step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38370step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38370step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw38370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38370 raw38370Labels = mixedMoment B node823 node823Labels := by
  calc
    mixedMoment B raw38370 raw38370Labels = mixedMoment B raw38370step0 raw38370step0Labels := by
      have ha : raw38370step0 = (fun i j => raw38370 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38370step0 raw38370; decide +kernel
      have hl : raw38370step0Labels = raw38370Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38370 raw38370Labels permutation44 permutation7
    mixedMoment B raw38370step0 raw38370step0Labels = mixedMoment B raw38370step1 raw38370step1Labels := by
      have ha : raw38370step1 = -raw38370step0 := by apply Matrix.ext; change ∀ i j, raw38370step1 i j = -(raw38370step0 i j); unfold raw38370step1 raw38370step0; decide +kernel
      have hl : raw38370step1Labels = raw38370step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38370step1 raw38370step1Labels = mixedMoment B raw38370step2 raw38370step2Labels := by
      have ha : raw38370step2 = raw38370step1 := by apply Matrix.ext; unfold raw38370step2 raw38370step1; decide +kernel
      have hl : raw38370step1Labels = labelEmbedding4 ∘ raw38370step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38370step1 raw38370step1Labels raw38370step2Labels labelEmbedding4 hl
    _ = mixedMoment B node823 node823Labels := by rfl

def raw38371 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38371Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38371 raw38371Labels = mixedMoment B node790 node790Labels := by
  calc
    mixedMoment B raw38371 raw38371Labels = mixedMoment B raw38371step0 raw38371step0Labels := by
      have ha : raw38371step0 = raw38371 := by apply Matrix.ext; unfold raw38371step0 raw38371; decide +kernel
      have hl : raw38371Labels = labelEmbedding2 ∘ raw38371step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38371 raw38371Labels raw38371step0Labels labelEmbedding2 hl
    _ = mixedMoment B node790 node790Labels := by rfl

def raw38372 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw38372Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw38372step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw38372step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw38372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38372 raw38372Labels = mixedMoment B node848 node848Labels := by
  calc
    mixedMoment B raw38372 raw38372Labels = mixedMoment B raw38372step0 raw38372step0Labels := by
      have ha : raw38372step0 = (fun i j => raw38372 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38372step0 raw38372; decide +kernel
      have hl : raw38372step0Labels = raw38372Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38372 raw38372Labels permutation32 permutation7
    mixedMoment B raw38372step0 raw38372step0Labels = mixedMoment B raw38372step1 raw38372step1Labels := by
      have ha : raw38372step1 = -raw38372step0 := by apply Matrix.ext; change ∀ i j, raw38372step1 i j = -(raw38372step0 i j); unfold raw38372step1 raw38372step0; decide +kernel
      have hl : raw38372step1Labels = raw38372step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38372step1 raw38372step1Labels = mixedMoment B raw38372step2 raw38372step2Labels := by
      have ha : raw38372step2 = raw38372step1 := by apply Matrix.ext; unfold raw38372step2 raw38372step1; decide +kernel
      have hl : raw38372step1Labels = labelEmbedding4 ∘ raw38372step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38372step1 raw38372step1Labels raw38372step2Labels labelEmbedding4 hl
    _ = mixedMoment B node848 node848Labels := by rfl

def raw38373 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw38373Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38373step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw38373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38373 raw38373Labels = mixedMoment B node791 node791Labels := by
  calc
    mixedMoment B raw38373 raw38373Labels = mixedMoment B raw38373step0 raw38373step0Labels := by
      have ha : raw38373step0 = raw38373 := by apply Matrix.ext; unfold raw38373step0 raw38373; decide +kernel
      have hl : raw38373Labels = labelEmbedding2 ∘ raw38373step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38373 raw38373Labels raw38373step0Labels labelEmbedding2 hl
    _ = mixedMoment B node791 node791Labels := by rfl

def raw38374 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![4, -2, -2]]
def raw38374Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38374step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-2, -2, 4]]
def raw38374step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw38374step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38374step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw38374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38374 raw38374Labels = mixedMoment B node849 node849Labels := by
  calc
    mixedMoment B raw38374 raw38374Labels = mixedMoment B raw38374step0 raw38374step0Labels := by
      have ha : raw38374step0 = (fun i j => raw38374 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38374step0 raw38374; decide +kernel
      have hl : raw38374step0Labels = raw38374Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38374 raw38374Labels permutation8 permutation7
    mixedMoment B raw38374step0 raw38374step0Labels = mixedMoment B raw38374step1 raw38374step1Labels := by
      have ha : raw38374step1 = -raw38374step0 := by apply Matrix.ext; change ∀ i j, raw38374step1 i j = -(raw38374step0 i j); unfold raw38374step1 raw38374step0; decide +kernel
      have hl : raw38374step1Labels = raw38374step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38374step1 raw38374step1Labels = mixedMoment B raw38374step2 raw38374step2Labels := by
      have ha : raw38374step2 = raw38374step1 := by apply Matrix.ext; unfold raw38374step2 raw38374step1; decide +kernel
      have hl : raw38374step1Labels = labelEmbedding4 ∘ raw38374step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38374step1 raw38374step1Labels raw38374step2Labels labelEmbedding4 hl
    _ = mixedMoment B node849 node849Labels := by rfl

def raw38375 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw38375Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw38375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38375 raw38375Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw38375 raw38375Labels = mixedMoment B raw38375step0 raw38375step0Labels := by
      have ha : raw38375step0 = raw38375 := by apply Matrix.ext; unfold raw38375step0 raw38375; decide +kernel
      have hl : raw38375Labels = labelEmbedding2 ∘ raw38375step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38375 raw38375Labels raw38375step0Labels labelEmbedding2 hl
    _ = mixedMoment B node807 node807Labels := by rfl

def raw38376 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw38376Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw38376step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw38376step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38376step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw38376step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38376 raw38376Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw38376 raw38376Labels = mixedMoment B raw38376step0 raw38376step0Labels := by
      have ha : raw38376step0 = (fun i j => raw38376 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38376step0 raw38376; decide +kernel
      have hl : raw38376step0Labels = raw38376Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38376 raw38376Labels permutation39 permutation7
    mixedMoment B raw38376step0 raw38376step0Labels = mixedMoment B raw38376step1 raw38376step1Labels := by
      have ha : raw38376step1 = -raw38376step0 := by apply Matrix.ext; change ∀ i j, raw38376step1 i j = -(raw38376step0 i j); unfold raw38376step1 raw38376step0; decide +kernel
      have hl : raw38376step1Labels = raw38376step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38376step1 raw38376step1Labels = mixedMoment B raw38376step2 raw38376step2Labels := by
      have ha : raw38376step2 = raw38376step1 := by apply Matrix.ext; unfold raw38376step2 raw38376step1; decide +kernel
      have hl : raw38376step1Labels = labelEmbedding4 ∘ raw38376step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38376step1 raw38376step1Labels raw38376step2Labels labelEmbedding4 hl
    _ = mixedMoment B node807 node807Labels := by rfl

def raw38377 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38377Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38377 raw38377Labels = mixedMoment B node811 node811Labels := by
  calc
    mixedMoment B raw38377 raw38377Labels = mixedMoment B raw38377step0 raw38377step0Labels := by
      have ha : raw38377step0 = raw38377 := by apply Matrix.ext; unfold raw38377step0 raw38377; decide +kernel
      have hl : raw38377Labels = labelEmbedding2 ∘ raw38377step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38377 raw38377Labels raw38377step0Labels labelEmbedding2 hl
    _ = mixedMoment B node811 node811Labels := by rfl

def raw38378 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw38378Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw38378step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38378step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38378step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw38378step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38378 raw38378Labels = mixedMoment B node824 node824Labels := by
  calc
    mixedMoment B raw38378 raw38378Labels = mixedMoment B raw38378step0 raw38378step0Labels := by
      have ha : raw38378step0 = (fun i j => raw38378 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38378step0 raw38378; decide +kernel
      have hl : raw38378step0Labels = raw38378Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38378 raw38378Labels permutation50 permutation7
    mixedMoment B raw38378step0 raw38378step0Labels = mixedMoment B raw38378step1 raw38378step1Labels := by
      have ha : raw38378step1 = -raw38378step0 := by apply Matrix.ext; change ∀ i j, raw38378step1 i j = -(raw38378step0 i j); unfold raw38378step1 raw38378step0; decide +kernel
      have hl : raw38378step1Labels = raw38378step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38378step1 raw38378step1Labels = mixedMoment B raw38378step2 raw38378step2Labels := by
      have ha : raw38378step2 = raw38378step1 := by apply Matrix.ext; unfold raw38378step2 raw38378step1; decide +kernel
      have hl : raw38378step1Labels = labelEmbedding4 ∘ raw38378step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38378step1 raw38378step1Labels raw38378step2Labels labelEmbedding4 hl
    _ = mixedMoment B node824 node824Labels := by rfl

def raw38379 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38379Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38379step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38379step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38379 raw38379Labels = mixedMoment B node813 node813Labels := by
  calc
    mixedMoment B raw38379 raw38379Labels = mixedMoment B raw38379step0 raw38379step0Labels := by
      have ha : raw38379step0 = raw38379 := by apply Matrix.ext; unfold raw38379step0 raw38379; decide +kernel
      have hl : raw38379Labels = labelEmbedding2 ∘ raw38379step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38379 raw38379Labels raw38379step0Labels labelEmbedding2 hl
    _ = mixedMoment B node813 node813Labels := by rfl

def raw38380 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw38380Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38380step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw38380step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38380step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw38380step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38380step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw38380step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38380 raw38380Labels = mixedMoment B node853 node853Labels := by
  calc
    mixedMoment B raw38380 raw38380Labels = mixedMoment B raw38380step0 raw38380step0Labels := by
      have ha : raw38380step0 = (fun i j => raw38380 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38380step0 raw38380; decide +kernel
      have hl : raw38380step0Labels = raw38380Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38380 raw38380Labels permutation9 permutation7
    mixedMoment B raw38380step0 raw38380step0Labels = mixedMoment B raw38380step1 raw38380step1Labels := by
      have ha : raw38380step1 = -raw38380step0 := by apply Matrix.ext; change ∀ i j, raw38380step1 i j = -(raw38380step0 i j); unfold raw38380step1 raw38380step0; decide +kernel
      have hl : raw38380step1Labels = raw38380step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38380step1 raw38380step1Labels = mixedMoment B raw38380step2 raw38380step2Labels := by
      have ha : raw38380step2 = raw38380step1 := by apply Matrix.ext; unfold raw38380step2 raw38380step1; decide +kernel
      have hl : raw38380step1Labels = labelEmbedding4 ∘ raw38380step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38380step1 raw38380step1Labels raw38380step2Labels labelEmbedding4 hl
    _ = mixedMoment B node853 node853Labels := by rfl

def raw38381 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38381Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38381step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38381 raw38381Labels = mixedMoment B node815 node815Labels := by
  calc
    mixedMoment B raw38381 raw38381Labels = mixedMoment B raw38381step0 raw38381step0Labels := by
      have ha : raw38381step0 = raw38381 := by apply Matrix.ext; unfold raw38381step0 raw38381; decide +kernel
      have hl : raw38381Labels = labelEmbedding2 ∘ raw38381step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38381 raw38381Labels raw38381step0Labels labelEmbedding2 hl
    _ = mixedMoment B node815 node815Labels := by rfl

def raw38382 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw38382Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38382step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw38382step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38382step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw38382step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38382step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw38382step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38382 raw38382Labels = mixedMoment B node826 node826Labels := by
  calc
    mixedMoment B raw38382 raw38382Labels = mixedMoment B raw38382step0 raw38382step0Labels := by
      have ha : raw38382step0 = (fun i j => raw38382 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38382step0 raw38382; decide +kernel
      have hl : raw38382step0Labels = raw38382Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38382 raw38382Labels permutation10 permutation7
    mixedMoment B raw38382step0 raw38382step0Labels = mixedMoment B raw38382step1 raw38382step1Labels := by
      have ha : raw38382step1 = -raw38382step0 := by apply Matrix.ext; change ∀ i j, raw38382step1 i j = -(raw38382step0 i j); unfold raw38382step1 raw38382step0; decide +kernel
      have hl : raw38382step1Labels = raw38382step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38382step1 raw38382step1Labels = mixedMoment B raw38382step2 raw38382step2Labels := by
      have ha : raw38382step2 = raw38382step1 := by apply Matrix.ext; unfold raw38382step2 raw38382step1; decide +kernel
      have hl : raw38382step1Labels = labelEmbedding4 ∘ raw38382step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38382step1 raw38382step1Labels raw38382step2Labels labelEmbedding4 hl
    _ = mixedMoment B node826 node826Labels := by rfl

def raw38383 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38383Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38383 raw38383Labels = mixedMoment B node827 node827Labels := by
  calc
    mixedMoment B raw38383 raw38383Labels = mixedMoment B raw38383step0 raw38383step0Labels := by
      have ha : raw38383step0 = raw38383 := by apply Matrix.ext; unfold raw38383step0 raw38383; decide +kernel
      have hl : raw38383Labels = labelEmbedding2 ∘ raw38383step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38383 raw38383Labels raw38383step0Labels labelEmbedding2 hl
    _ = mixedMoment B node827 node827Labels := by rfl

def raw38384 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38384Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw38384step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38384step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38384step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw38384step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38384 raw38384Labels = mixedMoment B node827 node827Labels := by
  calc
    mixedMoment B raw38384 raw38384Labels = mixedMoment B raw38384step0 raw38384step0Labels := by
      have ha : raw38384step0 = (fun i j => raw38384 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38384step0 raw38384; decide +kernel
      have hl : raw38384step0Labels = raw38384Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38384 raw38384Labels permutation53 permutation7
    mixedMoment B raw38384step0 raw38384step0Labels = mixedMoment B raw38384step1 raw38384step1Labels := by
      have ha : raw38384step1 = -raw38384step0 := by apply Matrix.ext; change ∀ i j, raw38384step1 i j = -(raw38384step0 i j); unfold raw38384step1 raw38384step0; decide +kernel
      have hl : raw38384step1Labels = raw38384step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38384step1 raw38384step1Labels = mixedMoment B raw38384step2 raw38384step2Labels := by
      have ha : raw38384step2 = raw38384step1 := by apply Matrix.ext; unfold raw38384step2 raw38384step1; decide +kernel
      have hl : raw38384step1Labels = labelEmbedding4 ∘ raw38384step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38384step1 raw38384step1Labels raw38384step2Labels labelEmbedding4 hl
    _ = mixedMoment B node827 node827Labels := by rfl

def raw38385 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw38385Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38385step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw38385step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38385 raw38385Labels = mixedMoment B node828 node828Labels := by
  calc
    mixedMoment B raw38385 raw38385Labels = mixedMoment B raw38385step0 raw38385step0Labels := by
      have ha : raw38385step0 = raw38385 := by apply Matrix.ext; unfold raw38385step0 raw38385; decide +kernel
      have hl : raw38385Labels = labelEmbedding2 ∘ raw38385step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38385 raw38385Labels raw38385step0Labels labelEmbedding2 hl
    _ = mixedMoment B node828 node828Labels := by rfl

def raw38386 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw38386Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38386step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw38386step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38386step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw38386step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38386step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw38386step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38386 raw38386Labels = mixedMoment B node857 node857Labels := by
  calc
    mixedMoment B raw38386 raw38386Labels = mixedMoment B raw38386step0 raw38386step0Labels := by
      have ha : raw38386step0 = (fun i j => raw38386 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38386step0 raw38386; decide +kernel
      have hl : raw38386step0Labels = raw38386Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38386 raw38386Labels permutation11 permutation7
    mixedMoment B raw38386step0 raw38386step0Labels = mixedMoment B raw38386step1 raw38386step1Labels := by
      have ha : raw38386step1 = -raw38386step0 := by apply Matrix.ext; change ∀ i j, raw38386step1 i j = -(raw38386step0 i j); unfold raw38386step1 raw38386step0; decide +kernel
      have hl : raw38386step1Labels = raw38386step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38386step1 raw38386step1Labels = mixedMoment B raw38386step2 raw38386step2Labels := by
      have ha : raw38386step2 = raw38386step1 := by apply Matrix.ext; unfold raw38386step2 raw38386step1; decide +kernel
      have hl : raw38386step1Labels = labelEmbedding4 ∘ raw38386step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38386step1 raw38386step1Labels raw38386step2Labels labelEmbedding4 hl
    _ = mixedMoment B node857 node857Labels := by rfl

def raw38387 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38387Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38387step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38387step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38387 raw38387Labels = mixedMoment B node830 node830Labels := by
  calc
    mixedMoment B raw38387 raw38387Labels = mixedMoment B raw38387step0 raw38387step0Labels := by
      have ha : raw38387step0 = raw38387 := by apply Matrix.ext; unfold raw38387step0 raw38387; decide +kernel
      have hl : raw38387Labels = labelEmbedding2 ∘ raw38387step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38387 raw38387Labels raw38387step0Labels labelEmbedding2 hl
    _ = mixedMoment B node830 node830Labels := by rfl

def raw38388 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38388Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38388step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw38388step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38388step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38388step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38388step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw38388step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38388 raw38388Labels = mixedMoment B node830 node830Labels := by
  calc
    mixedMoment B raw38388 raw38388Labels = mixedMoment B raw38388step0 raw38388step0Labels := by
      have ha : raw38388step0 = (fun i j => raw38388 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38388step0 raw38388; decide +kernel
      have hl : raw38388step0Labels = raw38388Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38388 raw38388Labels permutation10 permutation7
    mixedMoment B raw38388step0 raw38388step0Labels = mixedMoment B raw38388step1 raw38388step1Labels := by
      have ha : raw38388step1 = -raw38388step0 := by apply Matrix.ext; change ∀ i j, raw38388step1 i j = -(raw38388step0 i j); unfold raw38388step1 raw38388step0; decide +kernel
      have hl : raw38388step1Labels = raw38388step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38388step1 raw38388step1Labels = mixedMoment B raw38388step2 raw38388step2Labels := by
      have ha : raw38388step2 = raw38388step1 := by apply Matrix.ext; unfold raw38388step2 raw38388step1; decide +kernel
      have hl : raw38388step1Labels = labelEmbedding4 ∘ raw38388step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38388step1 raw38388step1Labels raw38388step2Labels labelEmbedding4 hl
    _ = mixedMoment B node830 node830Labels := by rfl

def raw38389 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38389Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38389step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38389step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38389 raw38389Labels = mixedMoment B node831 node831Labels := by
  calc
    mixedMoment B raw38389 raw38389Labels = mixedMoment B raw38389step0 raw38389step0Labels := by
      have ha : raw38389step0 = raw38389 := by apply Matrix.ext; unfold raw38389step0 raw38389; decide +kernel
      have hl : raw38389Labels = labelEmbedding2 ∘ raw38389step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38389 raw38389Labels raw38389step0Labels labelEmbedding2 hl
    _ = mixedMoment B node831 node831Labels := by rfl

def raw38390 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw38390Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38390step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw38390step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38390step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw38390step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38390step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw38390step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38390 raw38390Labels = mixedMoment B node858 node858Labels := by
  calc
    mixedMoment B raw38390 raw38390Labels = mixedMoment B raw38390step0 raw38390step0Labels := by
      have ha : raw38390step0 = (fun i j => raw38390 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38390step0 raw38390; decide +kernel
      have hl : raw38390step0Labels = raw38390Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38390 raw38390Labels permutation11 permutation7
    mixedMoment B raw38390step0 raw38390step0Labels = mixedMoment B raw38390step1 raw38390step1Labels := by
      have ha : raw38390step1 = -raw38390step0 := by apply Matrix.ext; change ∀ i j, raw38390step1 i j = -(raw38390step0 i j); unfold raw38390step1 raw38390step0; decide +kernel
      have hl : raw38390step1Labels = raw38390step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38390step1 raw38390step1Labels = mixedMoment B raw38390step2 raw38390step2Labels := by
      have ha : raw38390step2 = raw38390step1 := by apply Matrix.ext; unfold raw38390step2 raw38390step1; decide +kernel
      have hl : raw38390step1Labels = labelEmbedding4 ∘ raw38390step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38390step1 raw38390step1Labels raw38390step2Labels labelEmbedding4 hl
    _ = mixedMoment B node858 node858Labels := by rfl

def raw38391 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw38391Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38391step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw38391step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38391 raw38391Labels = mixedMoment B node832 node832Labels := by
  calc
    mixedMoment B raw38391 raw38391Labels = mixedMoment B raw38391step0 raw38391step0Labels := by
      have ha : raw38391step0 = raw38391 := by apply Matrix.ext; unfold raw38391step0 raw38391; decide +kernel
      have hl : raw38391Labels = labelEmbedding2 ∘ raw38391step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38391 raw38391Labels raw38391step0Labels labelEmbedding2 hl
    _ = mixedMoment B node832 node832Labels := by rfl

def raw38392 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![4, -2, -2]]
def raw38392Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38392step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-2, 2, 0], ![-2, -2, 4]]
def raw38392step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38392step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![2, -2, 0], ![2, 2, -4]]
def raw38392step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38392step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![2, -2, 0], ![2, 2, -4]]
def raw38392step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38392 raw38392Labels = mixedMoment B node862 node862Labels := by
  calc
    mixedMoment B raw38392 raw38392Labels = mixedMoment B raw38392step0 raw38392step0Labels := by
      have ha : raw38392step0 = (fun i j => raw38392 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38392step0 raw38392; decide +kernel
      have hl : raw38392step0Labels = raw38392Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38392 raw38392Labels permutation2 permutation7
    mixedMoment B raw38392step0 raw38392step0Labels = mixedMoment B raw38392step1 raw38392step1Labels := by
      have ha : raw38392step1 = -raw38392step0 := by apply Matrix.ext; change ∀ i j, raw38392step1 i j = -(raw38392step0 i j); unfold raw38392step1 raw38392step0; decide +kernel
      have hl : raw38392step1Labels = raw38392step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38392step1 raw38392step1Labels = mixedMoment B raw38392step2 raw38392step2Labels := by
      have ha : raw38392step2 = raw38392step1 := by apply Matrix.ext; unfold raw38392step2 raw38392step1; decide +kernel
      have hl : raw38392step1Labels = labelEmbedding4 ∘ raw38392step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38392step1 raw38392step1Labels raw38392step2Labels labelEmbedding4 hl
    _ = mixedMoment B node862 node862Labels := by rfl

def raw38393 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw38393Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38393step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw38393step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38393 raw38393Labels = mixedMoment B node860 node860Labels := by
  calc
    mixedMoment B raw38393 raw38393Labels = mixedMoment B raw38393step0 raw38393step0Labels := by
      have ha : raw38393step0 = raw38393 := by apply Matrix.ext; unfold raw38393step0 raw38393; decide +kernel
      have hl : raw38393Labels = labelEmbedding2 ∘ raw38393step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38393 raw38393Labels raw38393step0Labels labelEmbedding2 hl
    _ = mixedMoment B node860 node860Labels := by rfl

def raw38394 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw38394Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38394step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-1, -2, 3], ![-3, 2, 1]]
def raw38394step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38394step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw38394step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38394step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 2, -3], ![3, -2, -1]]
def raw38394step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38394 raw38394Labels = mixedMoment B node860 node860Labels := by
  calc
    mixedMoment B raw38394 raw38394Labels = mixedMoment B raw38394step0 raw38394step0Labels := by
      have ha : raw38394step0 = (fun i j => raw38394 (permutation3 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38394step0 raw38394; decide +kernel
      have hl : raw38394step0Labels = raw38394Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38394 raw38394Labels permutation3 permutation7
    mixedMoment B raw38394step0 raw38394step0Labels = mixedMoment B raw38394step1 raw38394step1Labels := by
      have ha : raw38394step1 = -raw38394step0 := by apply Matrix.ext; change ∀ i j, raw38394step1 i j = -(raw38394step0 i j); unfold raw38394step1 raw38394step0; decide +kernel
      have hl : raw38394step1Labels = raw38394step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38394step1 raw38394step1Labels = mixedMoment B raw38394step2 raw38394step2Labels := by
      have ha : raw38394step2 = raw38394step1 := by apply Matrix.ext; unfold raw38394step2 raw38394step1; decide +kernel
      have hl : raw38394step1Labels = labelEmbedding4 ∘ raw38394step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38394step1 raw38394step1Labels raw38394step2Labels labelEmbedding4 hl
    _ = mixedMoment B node860 node860Labels := by rfl

def raw38395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38395Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38395step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38395 raw38395Labels = mixedMoment B node864 node864Labels := by
  calc
    mixedMoment B raw38395 raw38395Labels = mixedMoment B raw38395step0 raw38395step0Labels := by
      have ha : raw38395step0 = raw38395 := by apply Matrix.ext; unfold raw38395step0 raw38395; decide +kernel
      have hl : raw38395Labels = labelEmbedding2 ∘ raw38395step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38395 raw38395Labels raw38395step0Labels labelEmbedding2 hl
    _ = mixedMoment B node864 node864Labels := by rfl

def raw38396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw38396Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw38396step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw38396step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38396step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw38396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38396 raw38396Labels = mixedMoment B node1550 node1550Labels := by
  calc
    mixedMoment B raw38396 raw38396Labels = mixedMoment B raw38396step0 raw38396step0Labels := by
      have ha : raw38396step0 = (fun i j => raw38396 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38396step0 raw38396; decide +kernel
      have hl : raw38396step0Labels = raw38396Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38396 raw38396Labels permutation160 permutation7
    mixedMoment B raw38396step0 raw38396step0Labels = mixedMoment B raw38396step1 raw38396step1Labels := by
      have ha : raw38396step1 = -raw38396step0 := by apply Matrix.ext; change ∀ i j, raw38396step1 i j = -(raw38396step0 i j); unfold raw38396step1 raw38396step0; decide +kernel
      have hl : raw38396step1Labels = raw38396step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38396step1 raw38396step1Labels = mixedMoment B raw38396step2 raw38396step2Labels := by
      have ha : raw38396step2 = raw38396step1 := by apply Matrix.ext; unfold raw38396step2 raw38396step1; decide +kernel
      have hl : raw38396step1Labels = labelEmbedding4 ∘ raw38396step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38396step1 raw38396step1Labels raw38396step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1550 node1550Labels := by rfl

def raw38397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38397Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38397 raw38397Labels = mixedMoment B node865 node865Labels := by
  calc
    mixedMoment B raw38397 raw38397Labels = mixedMoment B raw38397step0 raw38397step0Labels := by
      have ha : raw38397step0 = raw38397 := by apply Matrix.ext; unfold raw38397step0 raw38397; decide +kernel
      have hl : raw38397Labels = labelEmbedding2 ∘ raw38397step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38397 raw38397Labels raw38397step0Labels labelEmbedding2 hl
    _ = mixedMoment B node865 node865Labels := by rfl

def raw38398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw38398Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw38398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw38398step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38398step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw38398step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw38398step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38398 raw38398Labels = mixedMoment B node1553 node1553Labels := by
  calc
    mixedMoment B raw38398 raw38398Labels = mixedMoment B raw38398step0 raw38398step0Labels := by
      have ha : raw38398step0 = (fun i j => raw38398 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw38398step0 raw38398; decide +kernel
      have hl : raw38398step0Labels = raw38398Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw38398 raw38398Labels permutation158 permutation7
    mixedMoment B raw38398step0 raw38398step0Labels = mixedMoment B raw38398step1 raw38398step1Labels := by
      have ha : raw38398step1 = -raw38398step0 := by apply Matrix.ext; change ∀ i j, raw38398step1 i j = -(raw38398step0 i j); unfold raw38398step1 raw38398step0; decide +kernel
      have hl : raw38398step1Labels = raw38398step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw38398step1 raw38398step1Labels = mixedMoment B raw38398step2 raw38398step2Labels := by
      have ha : raw38398step2 = raw38398step1 := by apply Matrix.ext; unfold raw38398step2 raw38398step1; decide +kernel
      have hl : raw38398step1Labels = labelEmbedding4 ∘ raw38398step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38398step1 raw38398step1Labels raw38398step2Labels labelEmbedding4 hl
    _ = mixedMoment B node1553 node1553Labels := by rfl

def raw38399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38399Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw38399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw38399step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical38399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw38399 raw38399Labels = mixedMoment B node866 node866Labels := by
  calc
    mixedMoment B raw38399 raw38399Labels = mixedMoment B raw38399step0 raw38399step0Labels := by
      have ha : raw38399step0 = raw38399 := by apply Matrix.ext; unfold raw38399step0 raw38399; decide +kernel
      have hl : raw38399Labels = labelEmbedding2 ∘ raw38399step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw38399 raw38399Labels raw38399step0Labels labelEmbedding2 hl
    _ = mixedMoment B node866 node866Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
