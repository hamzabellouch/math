import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw27264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw27264step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27264step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27264step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27264step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27264 raw27264Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw27264 raw27264Labels = mixedMoment B raw27264step0 raw27264step0Labels := by
      have ha : raw27264step0 = (fun i j => raw27264 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27264step0 raw27264; decide +kernel
      have hl : raw27264step0Labels = raw27264Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27264 raw27264Labels permutation246 permutation7
    mixedMoment B raw27264step0 raw27264step0Labels = mixedMoment B raw27264step1 raw27264step1Labels := by
      have ha : raw27264step1 = -raw27264step0 := by apply Matrix.ext; change ∀ i j, raw27264step1 i j = -(raw27264step0 i j); unfold raw27264step1 raw27264step0; decide +kernel
      have hl : raw27264step1Labels = raw27264step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27264step1 raw27264step1Labels = mixedMoment B raw27264step2 raw27264step2Labels := by
      have ha : raw27264step2 = raw27264step1 := by apply Matrix.ext; unfold raw27264step2 raw27264step1; decide +kernel
      have hl : raw27264step1Labels = labelEmbedding10 ∘ raw27264step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27264step1 raw27264step1Labels raw27264step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw27265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw27265step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27265step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27265step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27265step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27265 raw27265Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw27265 raw27265Labels = mixedMoment B raw27265step0 raw27265step0Labels := by
      have ha : raw27265step0 = (fun i j => raw27265 (permutation248 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27265step0 raw27265; decide +kernel
      have hl : raw27265step0Labels = raw27265Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27265 raw27265Labels permutation248 permutation7
    mixedMoment B raw27265step0 raw27265step0Labels = mixedMoment B raw27265step1 raw27265step1Labels := by
      have ha : raw27265step1 = -raw27265step0 := by apply Matrix.ext; change ∀ i j, raw27265step1 i j = -(raw27265step0 i j); unfold raw27265step1 raw27265step0; decide +kernel
      have hl : raw27265step1Labels = raw27265step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27265step1 raw27265step1Labels = mixedMoment B raw27265step2 raw27265step2Labels := by
      have ha : raw27265step2 = raw27265step1 := by apply Matrix.ext; unfold raw27265step2 raw27265step1; decide +kernel
      have hl : raw27265step1Labels = labelEmbedding10 ∘ raw27265step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27265step1 raw27265step1Labels raw27265step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw27266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw27266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw27266step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27266step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27266step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27266step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27266step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27266 raw27266Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw27266 raw27266Labels = mixedMoment B raw27266step0 raw27266step0Labels := by
      have ha : raw27266step0 = (fun i j => raw27266 (permutation250 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27266step0 raw27266; decide +kernel
      have hl : raw27266step0Labels = raw27266Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27266 raw27266Labels permutation250 permutation7
    mixedMoment B raw27266step0 raw27266step0Labels = mixedMoment B raw27266step1 raw27266step1Labels := by
      have ha : raw27266step1 = -raw27266step0 := by apply Matrix.ext; change ∀ i j, raw27266step1 i j = -(raw27266step0 i j); unfold raw27266step1 raw27266step0; decide +kernel
      have hl : raw27266step1Labels = raw27266step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27266step1 raw27266step1Labels = mixedMoment B raw27266step2 raw27266step2Labels := by
      have ha : raw27266step2 = raw27266step1 := by apply Matrix.ext; unfold raw27266step2 raw27266step1; decide +kernel
      have hl : raw27266step1Labels = labelEmbedding10 ∘ raw27266step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27266step1 raw27266step1Labels raw27266step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw27267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw27267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27267step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27267step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27267step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27267step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27267 raw27267Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw27267 raw27267Labels = mixedMoment B raw27267step0 raw27267step0Labels := by
      have hz : ∀ j, raw27267 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27267step0 = (fun i j => raw27267 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27267step0 raw27267; decide +kernel
      have hl : raw27267step0Labels = raw27267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27267 raw27267Labels permutation590 hz
    mixedMoment B raw27267step0 raw27267step0Labels = mixedMoment B raw27267step1 raw27267step1Labels := by
      have ha : raw27267step1 = (fun i j => raw27267step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27267step1 raw27267step0; decide +kernel
      have hl : raw27267step1Labels = raw27267step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27267step0 raw27267step0Labels permutation32 permutation7
    mixedMoment B raw27267step1 raw27267step1Labels = mixedMoment B raw27267step2 raw27267step2Labels := by
      have ha : raw27267step2 = -raw27267step1 := by apply Matrix.ext; change ∀ i j, raw27267step2 i j = -(raw27267step1 i j); unfold raw27267step2 raw27267step1; decide +kernel
      have hl : raw27267step2Labels = raw27267step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27267step2 raw27267step2Labels = mixedMoment B raw27267step3 raw27267step3Labels := by
      have ha : raw27267step3 = raw27267step2 := by apply Matrix.ext; unfold raw27267step3 raw27267step2; decide +kernel
      have hl : raw27267step2Labels = labelEmbedding10 ∘ raw27267step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27267step2 raw27267step2Labels raw27267step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4497 node4497Labels := by rfl

def raw27268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27268 raw27268Labels = mixedMoment B node4117 node4117Labels := by
  calc
    mixedMoment B raw27268 raw27268Labels = mixedMoment B raw27268step0 raw27268step0Labels := by
      have ha : raw27268step0 = (fun i j => raw27268 (permutation246 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27268step0 raw27268; decide +kernel
      have hl : raw27268step0Labels = raw27268Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27268 raw27268Labels permutation246 permutation2
    _ = mixedMoment B node4117 node4117Labels := by rfl

def raw27269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27269 raw27269Labels = mixedMoment B node4263 node4263Labels := by
  calc
    mixedMoment B raw27269 raw27269Labels = mixedMoment B raw27269step0 raw27269step0Labels := by
      have ha : raw27269step0 = (fun i j => raw27269 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27269step0 raw27269; decide +kernel
      have hl : raw27269step0Labels = raw27269Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27269 raw27269Labels permutation194 permutation2
    _ = mixedMoment B node4263 node4263Labels := by rfl

def raw27270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27270step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27270 raw27270Labels = mixedMoment B node4263 node4263Labels := by
  calc
    mixedMoment B raw27270 raw27270Labels = mixedMoment B raw27270step0 raw27270step0Labels := by
      have ha : raw27270step0 = (fun i j => raw27270 (permutation218 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27270step0 raw27270; decide +kernel
      have hl : raw27270step0Labels = raw27270Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27270 raw27270Labels permutation218 permutation2
    _ = mixedMoment B node4263 node4263Labels := by rfl

def raw27271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw27271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27271 raw27271Labels = mixedMoment B node4263 node4263Labels := by
  calc
    mixedMoment B raw27271 raw27271Labels = mixedMoment B raw27271step0 raw27271step0Labels := by
      have ha : raw27271step0 = (fun i j => raw27271 (permutation240 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27271step0 raw27271; decide +kernel
      have hl : raw27271step0Labels = raw27271Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27271 raw27271Labels permutation240 permutation2
    _ = mixedMoment B node4263 node4263Labels := by rfl

def raw27272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw27272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27272step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27272step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw27272step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw27272step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw27272step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27272 raw27272Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw27272 raw27272Labels = mixedMoment B raw27272step0 raw27272step0Labels := by
      have hz : ∀ j, raw27272 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27272step0 = (fun i j => raw27272 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27272step0 raw27272; decide +kernel
      have hl : raw27272step0Labels = raw27272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27272 raw27272Labels permutation590 hz
    mixedMoment B raw27272step0 raw27272step0Labels = mixedMoment B raw27272step1 raw27272step1Labels := by
      have hz : ∀ i, raw27272step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw27272step1 = (fun i j => raw27272step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw27272step1 raw27272step0; decide +kernel
      have hl : raw27272step1Labels = (fun j => raw27272step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27272step0 raw27272step0Labels permutation4 hz
    mixedMoment B raw27272step1 raw27272step1Labels = mixedMoment B raw27272step2 raw27272step2Labels := by
      have ha : raw27272step2 = raw27272step1 := by apply Matrix.ext; unfold raw27272step2 raw27272step1; decide +kernel
      have hl : raw27272step1Labels = labelEmbedding2 ∘ raw27272step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27272step1 raw27272step1Labels raw27272step2Labels labelEmbedding2 hl
    _ = mixedMoment B node4068 node4068Labels := by rfl

def raw27273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27273step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27273 raw27273Labels = mixedMoment B node4100 node4100Labels := by
  calc
    mixedMoment B raw27273 raw27273Labels = mixedMoment B raw27273step0 raw27273step0Labels := by
      have ha : raw27273step0 = (fun i j => raw27273 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27273step0 raw27273; decide +kernel
      have hl : raw27273step0Labels = raw27273Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27273 raw27273Labels permutation173 permutation2
    _ = mixedMoment B node4100 node4100Labels := by rfl

def raw27274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27274step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27274 raw27274Labels = mixedMoment B node4232 node4232Labels := by
  calc
    mixedMoment B raw27274 raw27274Labels = mixedMoment B raw27274step0 raw27274step0Labels := by
      have ha : raw27274step0 = (fun i j => raw27274 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27274step0 raw27274; decide +kernel
      have hl : raw27274step0Labels = raw27274Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27274 raw27274Labels permutation173 permutation2
    _ = mixedMoment B node4232 node4232Labels := by rfl

def raw27275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27275 raw27275Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw27275 raw27275Labels = mixedMoment B raw27275step0 raw27275step0Labels := by
      have ha : raw27275step0 = (fun i j => raw27275 (permutation163 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27275step0 raw27275; decide +kernel
      have hl : raw27275step0Labels = raw27275Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27275 raw27275Labels permutation163 permutation2
    _ = mixedMoment B node4249 node4249Labels := by rfl

def raw27276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw27276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27276 raw27276Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw27276 raw27276Labels = mixedMoment B raw27276step0 raw27276step0Labels := by
      have ha : raw27276step0 = (fun i j => raw27276 (permutation169 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27276step0 raw27276; decide +kernel
      have hl : raw27276step0Labels = raw27276Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27276 raw27276Labels permutation169 permutation2
    _ = mixedMoment B node4249 node4249Labels := by rfl

def raw27277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw27277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27277step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27277 raw27277Labels = mixedMoment B node4267 node4267Labels := by
  calc
    mixedMoment B raw27277 raw27277Labels = mixedMoment B raw27277step0 raw27277step0Labels := by
      have hz : ∀ j, raw27277 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27277step0 = (fun i j => raw27277 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27277step0 raw27277; decide +kernel
      have hl : raw27277step0Labels = raw27277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27277 raw27277Labels permutation590 hz
    mixedMoment B raw27277step0 raw27277step0Labels = mixedMoment B raw27277step1 raw27277step1Labels := by
      have ha : raw27277step1 = (fun i j => raw27277step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27277step1 raw27277step0; decide +kernel
      have hl : raw27277step1Labels = raw27277step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27277step0 raw27277step0Labels permutation35 permutation2
    _ = mixedMoment B node4267 node4267Labels := by rfl

def raw27278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27278 raw27278Labels = mixedMoment B node4100 node4100Labels := by
  calc
    mixedMoment B raw27278 raw27278Labels = mixedMoment B raw27278step0 raw27278step0Labels := by
      have ha : raw27278step0 = (fun i j => raw27278 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27278step0 raw27278; decide +kernel
      have hl : raw27278step0Labels = raw27278Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27278 raw27278Labels permutation171 permutation2
    _ = mixedMoment B node4100 node4100Labels := by rfl

def raw27279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27279 raw27279Labels = mixedMoment B node4232 node4232Labels := by
  calc
    mixedMoment B raw27279 raw27279Labels = mixedMoment B raw27279step0 raw27279step0Labels := by
      have ha : raw27279step0 = (fun i j => raw27279 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27279step0 raw27279; decide +kernel
      have hl : raw27279step0Labels = raw27279Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27279 raw27279Labels permutation171 permutation2
    _ = mixedMoment B node4232 node4232Labels := by rfl

def raw27280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw27280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27280 raw27280Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw27280 raw27280Labels = mixedMoment B raw27280step0 raw27280step0Labels := by
      have ha : raw27280step0 = (fun i j => raw27280 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27280step0 raw27280; decide +kernel
      have hl : raw27280step0Labels = raw27280Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27280 raw27280Labels permutation157 permutation2
    _ = mixedMoment B node4249 node4249Labels := by rfl

def raw27281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw27281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27281 raw27281Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw27281 raw27281Labels = mixedMoment B raw27281step0 raw27281step0Labels := by
      have ha : raw27281step0 = (fun i j => raw27281 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27281step0 raw27281; decide +kernel
      have hl : raw27281step0Labels = raw27281Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27281 raw27281Labels permutation168 permutation2
    _ = mixedMoment B node4249 node4249Labels := by rfl

def raw27282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw27282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw27282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27282 raw27282Labels = mixedMoment B node4267 node4267Labels := by
  calc
    mixedMoment B raw27282 raw27282Labels = mixedMoment B raw27282step0 raw27282step0Labels := by
      have hz : ∀ j, raw27282 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27282step0 = (fun i j => raw27282 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27282step0 raw27282; decide +kernel
      have hl : raw27282step0Labels = raw27282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27282 raw27282Labels permutation590 hz
    mixedMoment B raw27282step0 raw27282step0Labels = mixedMoment B raw27282step1 raw27282step1Labels := by
      have ha : raw27282step1 = (fun i j => raw27282step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27282step1 raw27282step0; decide +kernel
      have hl : raw27282step1Labels = raw27282step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27282step0 raw27282step0Labels permutation33 permutation2
    _ = mixedMoment B node4267 node4267Labels := by rfl

def raw27283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw27283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27283step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27283 raw27283Labels = mixedMoment B node4100 node4100Labels := by
  calc
    mixedMoment B raw27283 raw27283Labels = mixedMoment B raw27283step0 raw27283step0Labels := by
      have ha : raw27283step0 = (fun i j => raw27283 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27283step0 raw27283; decide +kernel
      have hl : raw27283step0Labels = raw27283Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27283 raw27283Labels permutation170 permutation2
    _ = mixedMoment B node4100 node4100Labels := by rfl

def raw27284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw27284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27284 raw27284Labels = mixedMoment B node4232 node4232Labels := by
  calc
    mixedMoment B raw27284 raw27284Labels = mixedMoment B raw27284step0 raw27284step0Labels := by
      have ha : raw27284step0 = (fun i j => raw27284 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27284step0 raw27284; decide +kernel
      have hl : raw27284step0Labels = raw27284Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27284 raw27284Labels permutation170 permutation2
    _ = mixedMoment B node4232 node4232Labels := by rfl

def raw27285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw27285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27285 raw27285Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw27285 raw27285Labels = mixedMoment B raw27285step0 raw27285step0Labels := by
      have ha : raw27285step0 = (fun i j => raw27285 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27285step0 raw27285; decide +kernel
      have hl : raw27285step0Labels = raw27285Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27285 raw27285Labels permutation156 permutation2
    _ = mixedMoment B node4249 node4249Labels := by rfl

def raw27286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw27286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27286 raw27286Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw27286 raw27286Labels = mixedMoment B raw27286step0 raw27286step0Labels := by
      have ha : raw27286step0 = (fun i j => raw27286 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27286step0 raw27286; decide +kernel
      have hl : raw27286step0Labels = raw27286Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27286 raw27286Labels permutation162 permutation2
    _ = mixedMoment B node4249 node4249Labels := by rfl

def raw27287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw27287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27287 raw27287Labels = mixedMoment B node4267 node4267Labels := by
  calc
    mixedMoment B raw27287 raw27287Labels = mixedMoment B raw27287step0 raw27287step0Labels := by
      have hz : ∀ j, raw27287 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27287step0 = (fun i j => raw27287 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27287step0 raw27287; decide +kernel
      have hl : raw27287step0Labels = raw27287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27287 raw27287Labels permutation590 hz
    _ = mixedMoment B node4267 node4267Labels := by rfl

def raw27288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27288 raw27288Labels = mixedMoment B node4104 node4104Labels := by
  calc
    _ = mixedMoment B node4104 node4104Labels := by rfl

def raw27289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27289 raw27289Labels = mixedMoment B node4236 node4236Labels := by
  calc
    _ = mixedMoment B node4236 node4236Labels := by rfl

def raw27290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27290 raw27290Labels = mixedMoment B node4252 node4252Labels := by
  calc
    _ = mixedMoment B node4252 node4252Labels := by rfl

def raw27291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27291 raw27291Labels = mixedMoment B node4252 node4252Labels := by
  calc
    mixedMoment B raw27291 raw27291Labels = mixedMoment B raw27291step0 raw27291step0Labels := by
      have ha : raw27291step0 = (fun i j => raw27291 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27291step0 raw27291; decide +kernel
      have hl : raw27291step0Labels = raw27291Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27291 raw27291Labels permutation158 permutation2
    _ = mixedMoment B node4252 node4252Labels := by rfl

def raw27292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw27292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27292 raw27292Labels = mixedMoment B node4252 node4252Labels := by
  calc
    mixedMoment B raw27292 raw27292Labels = mixedMoment B raw27292step0 raw27292step0Labels := by
      have ha : raw27292step0 = (fun i j => raw27292 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27292step0 raw27292; decide +kernel
      have hl : raw27292step0Labels = raw27292Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27292 raw27292Labels permutation164 permutation2
    _ = mixedMoment B node4252 node4252Labels := by rfl

def raw27293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27293Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27293step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw27293step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27293 raw27293Labels = mixedMoment B node4056 node4056Labels := by
  calc
    mixedMoment B raw27293 raw27293Labels = mixedMoment B raw27293step0 raw27293step0Labels := by
      have hz : ∀ i, raw27293 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27293step0 = (fun i j => raw27293 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27293step0 raw27293; decide +kernel
      have hl : raw27293step0Labels = (fun j => raw27293Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27293 raw27293Labels permutation6 hz
    _ = mixedMoment B node4056 node4056Labels := by rfl

def raw27294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27294Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27294step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27294step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw27294step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27294 raw27294Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw27294 raw27294Labels = mixedMoment B raw27294step0 raw27294step0Labels := by
      have hz : ∀ j, raw27294 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27294step0 = (fun i j => raw27294 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27294step0 raw27294; decide +kernel
      have hl : raw27294step0Labels = raw27294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27294 raw27294Labels permutation434 hz
    mixedMoment B raw27294step0 raw27294step0Labels = mixedMoment B raw27294step1 raw27294step1Labels := by
      have hz : ∀ i, raw27294step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27294step1 = (fun i j => raw27294step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27294step1 raw27294step0; decide +kernel
      have hl : raw27294step1Labels = (fun j => raw27294step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27294step0 raw27294step0Labels permutation6 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

def raw27295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw27295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27295step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27295step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw27295step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27295 raw27295Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw27295 raw27295Labels = mixedMoment B raw27295step0 raw27295step0Labels := by
      have hz : ∀ j, raw27295 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27295step0 = (fun i j => raw27295 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27295step0 raw27295; decide +kernel
      have hl : raw27295step0Labels = raw27295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27295 raw27295Labels permutation520 hz
    mixedMoment B raw27295step0 raw27295step0Labels = mixedMoment B raw27295step1 raw27295step1Labels := by
      have hz : ∀ i, raw27295step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27295step1 = (fun i j => raw27295step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27295step1 raw27295step0; decide +kernel
      have hl : raw27295step1Labels = (fun j => raw27295step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27295step0 raw27295step0Labels permutation6 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

def raw27296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw27296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27296step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27296step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw27296step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27296 raw27296Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw27296 raw27296Labels = mixedMoment B raw27296step0 raw27296step0Labels := by
      have hz : ∀ j, raw27296 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27296step0 = (fun i j => raw27296 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27296step0 raw27296; decide +kernel
      have hl : raw27296step0Labels = raw27296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27296 raw27296Labels permutation590 hz
    mixedMoment B raw27296step0 raw27296step0Labels = mixedMoment B raw27296step1 raw27296step1Labels := by
      have hz : ∀ i, raw27296step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27296step1 = (fun i j => raw27296step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27296step1 raw27296step0; decide +kernel
      have hl : raw27296step1Labels = (fun j => raw27296step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27296step0 raw27296step0Labels permutation6 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

def raw27297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27297step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27297step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![1, -1], ![1, -1], ![1, -1]]
def raw27297step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27297step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw27297step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27297 raw27297Labels = mixedMoment B node4057 node4057Labels := by
  calc
    mixedMoment B raw27297 raw27297Labels = mixedMoment B raw27297step0 raw27297step0Labels := by
      have hz : ∀ j, raw27297 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27297step0 = (fun i j => raw27297 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27297step0 raw27297; decide +kernel
      have hl : raw27297step0Labels = raw27297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27297 raw27297Labels permutation265 hz
    mixedMoment B raw27297step0 raw27297step0Labels = mixedMoment B raw27297step1 raw27297step1Labels := by
      have hz : ∀ i, raw27297step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27297step1 = (fun i j => raw27297step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27297step1 raw27297step0; decide +kernel
      have hl : raw27297step1Labels = (fun j => raw27297step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27297step0 raw27297step0Labels permutation6 hz
    mixedMoment B raw27297step1 raw27297step1Labels = mixedMoment B raw27297step2 raw27297step2Labels := by
      have ha : raw27297step2 = (fun i j => raw27297step1 (permutation41 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27297step2 raw27297step1; decide +kernel
      have hl : raw27297step2Labels = raw27297step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27297step1 raw27297step1Labels permutation41 permutation0
    _ = mixedMoment B node4057 node4057Labels := by rfl

def raw27298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27298step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![1, -1], ![1, -1], ![1, -1]]
def raw27298step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27298step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw27298step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27298 raw27298Labels = mixedMoment B node4063 node4063Labels := by
  calc
    mixedMoment B raw27298 raw27298Labels = mixedMoment B raw27298step0 raw27298step0Labels := by
      have hz : ∀ i, raw27298 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27298step0 = (fun i j => raw27298 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27298step0 raw27298; decide +kernel
      have hl : raw27298step0Labels = (fun j => raw27298Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27298 raw27298Labels permutation6 hz
    mixedMoment B raw27298step0 raw27298step0Labels = mixedMoment B raw27298step1 raw27298step1Labels := by
      have ha : raw27298step1 = (fun i j => raw27298step0 (permutation161 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27298step1 raw27298step0; decide +kernel
      have hl : raw27298step1Labels = raw27298step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27298step0 raw27298step0Labels permutation161 permutation0
    _ = mixedMoment B node4063 node4063Labels := by rfl

def raw27299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27299step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27299step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27299step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![1, -1]]
def raw27299step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27299step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw27299step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27299 raw27299Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw27299 raw27299Labels = mixedMoment B raw27299step0 raw27299step0Labels := by
      have hz : ∀ j, raw27299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27299step0 = (fun i j => raw27299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27299step0 raw27299; decide +kernel
      have hl : raw27299step0Labels = raw27299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27299 raw27299Labels permutation434 hz
    mixedMoment B raw27299step0 raw27299step0Labels = mixedMoment B raw27299step1 raw27299step1Labels := by
      have hz : ∀ j, raw27299step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27299step1 = (fun i j => raw27299step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27299step1 raw27299step0; decide +kernel
      have hl : raw27299step1Labels = raw27299step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27299step0 raw27299step0Labels permutation56 hz
    mixedMoment B raw27299step1 raw27299step1Labels = mixedMoment B raw27299step2 raw27299step2Labels := by
      have hz : ∀ i, raw27299step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27299step2 = (fun i j => raw27299step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27299step2 raw27299step1; decide +kernel
      have hl : raw27299step2Labels = (fun j => raw27299step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27299step1 raw27299step1Labels permutation6 hz
    mixedMoment B raw27299step2 raw27299step2Labels = mixedMoment B raw27299step3 raw27299step3Labels := by
      have ha : raw27299step3 = (fun i j => raw27299step2 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27299step3 raw27299step2; decide +kernel
      have hl : raw27299step3Labels = raw27299step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27299step2 raw27299step2Labels permutation11 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw27300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw27300Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27300step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27300step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27300step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27300step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![1, -1]]
def raw27300step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27300step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw27300step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27300 raw27300Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw27300 raw27300Labels = mixedMoment B raw27300step0 raw27300step0Labels := by
      have hz : ∀ j, raw27300 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27300step0 = (fun i j => raw27300 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27300step0 raw27300; decide +kernel
      have hl : raw27300step0Labels = raw27300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27300 raw27300Labels permutation520 hz
    mixedMoment B raw27300step0 raw27300step0Labels = mixedMoment B raw27300step1 raw27300step1Labels := by
      have hz : ∀ j, raw27300step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27300step1 = (fun i j => raw27300step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27300step1 raw27300step0; decide +kernel
      have hl : raw27300step1Labels = raw27300step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27300step0 raw27300step0Labels permutation56 hz
    mixedMoment B raw27300step1 raw27300step1Labels = mixedMoment B raw27300step2 raw27300step2Labels := by
      have hz : ∀ i, raw27300step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27300step2 = (fun i j => raw27300step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27300step2 raw27300step1; decide +kernel
      have hl : raw27300step2Labels = (fun j => raw27300step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27300step1 raw27300step1Labels permutation6 hz
    mixedMoment B raw27300step2 raw27300step2Labels = mixedMoment B raw27300step3 raw27300step3Labels := by
      have ha : raw27300step3 = (fun i j => raw27300step2 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27300step3 raw27300step2; decide +kernel
      have hl : raw27300step3Labels = raw27300step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27300step2 raw27300step2Labels permutation11 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw27301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw27301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27301step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27301step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![1, -1]]
def raw27301step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27301step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw27301step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27301 raw27301Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw27301 raw27301Labels = mixedMoment B raw27301step0 raw27301step0Labels := by
      have hz : ∀ j, raw27301 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27301step0 = (fun i j => raw27301 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27301step0 raw27301; decide +kernel
      have hl : raw27301step0Labels = raw27301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27301 raw27301Labels permutation590 hz
    mixedMoment B raw27301step0 raw27301step0Labels = mixedMoment B raw27301step1 raw27301step1Labels := by
      have hz : ∀ j, raw27301step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27301step1 = (fun i j => raw27301step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27301step1 raw27301step0; decide +kernel
      have hl : raw27301step1Labels = raw27301step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27301step0 raw27301step0Labels permutation56 hz
    mixedMoment B raw27301step1 raw27301step1Labels = mixedMoment B raw27301step2 raw27301step2Labels := by
      have hz : ∀ i, raw27301step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27301step2 = (fun i j => raw27301step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27301step2 raw27301step1; decide +kernel
      have hl : raw27301step2Labels = (fun j => raw27301step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27301step1 raw27301step1Labels permutation6 hz
    mixedMoment B raw27301step2 raw27301step2Labels = mixedMoment B raw27301step3 raw27301step3Labels := by
      have ha : raw27301step3 = (fun i j => raw27301step2 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27301step3 raw27301step2; decide +kernel
      have hl : raw27301step3Labels = raw27301step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27301step2 raw27301step2Labels permutation11 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw27302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27302step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27302step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![1, -1], ![1, -1]]
def raw27302step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27302step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw27302step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27302 raw27302Labels = mixedMoment B node4057 node4057Labels := by
  calc
    mixedMoment B raw27302 raw27302Labels = mixedMoment B raw27302step0 raw27302step0Labels := by
      have hz : ∀ j, raw27302 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27302step0 = (fun i j => raw27302 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27302step0 raw27302; decide +kernel
      have hl : raw27302step0Labels = raw27302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27302 raw27302Labels permutation265 hz
    mixedMoment B raw27302step0 raw27302step0Labels = mixedMoment B raw27302step1 raw27302step1Labels := by
      have hz : ∀ i, raw27302step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27302step1 = (fun i j => raw27302step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27302step1 raw27302step0; decide +kernel
      have hl : raw27302step1Labels = (fun j => raw27302step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27302step0 raw27302step0Labels permutation6 hz
    mixedMoment B raw27302step1 raw27302step1Labels = mixedMoment B raw27302step2 raw27302step2Labels := by
      have ha : raw27302step2 = (fun i j => raw27302step1 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27302step2 raw27302step1; decide +kernel
      have hl : raw27302step2Labels = raw27302step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27302step1 raw27302step1Labels permutation35 permutation0
    _ = mixedMoment B node4057 node4057Labels := by rfl

def raw27303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw27303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27303step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![1, -1], ![1, -1]]
def raw27303step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27303step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw27303step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27303 raw27303Labels = mixedMoment B node4063 node4063Labels := by
  calc
    mixedMoment B raw27303 raw27303Labels = mixedMoment B raw27303step0 raw27303step0Labels := by
      have hz : ∀ i, raw27303 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27303step0 = (fun i j => raw27303 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27303step0 raw27303; decide +kernel
      have hl : raw27303step0Labels = (fun j => raw27303Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27303 raw27303Labels permutation6 hz
    mixedMoment B raw27303step0 raw27303step0Labels = mixedMoment B raw27303step1 raw27303step1Labels := by
      have ha : raw27303step1 = (fun i j => raw27303step0 (permutation155 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27303step1 raw27303step0; decide +kernel
      have hl : raw27303step1Labels = raw27303step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27303step0 raw27303step0Labels permutation155 permutation0
    _ = mixedMoment B node4063 node4063Labels := by rfl

def raw27304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw27304Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw27304step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw27304step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27304step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]
def raw27304step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27304step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw27304step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27304 raw27304Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw27304 raw27304Labels = mixedMoment B raw27304step0 raw27304step0Labels := by
      have hz : ∀ j, raw27304 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27304step0 = (fun i j => raw27304 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27304step0 raw27304; decide +kernel
      have hl : raw27304step0Labels = raw27304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27304 raw27304Labels permutation520 hz
    mixedMoment B raw27304step0 raw27304step0Labels = mixedMoment B raw27304step1 raw27304step1Labels := by
      have hz : ∀ j, raw27304step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27304step1 = (fun i j => raw27304step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27304step1 raw27304step0; decide +kernel
      have hl : raw27304step1Labels = raw27304step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27304step0 raw27304step0Labels permutation56 hz
    mixedMoment B raw27304step1 raw27304step1Labels = mixedMoment B raw27304step2 raw27304step2Labels := by
      have hz : ∀ i, raw27304step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27304step2 = (fun i j => raw27304step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27304step2 raw27304step1; decide +kernel
      have hl : raw27304step2Labels = (fun j => raw27304step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27304step1 raw27304step1Labels permutation6 hz
    mixedMoment B raw27304step2 raw27304step2Labels = mixedMoment B raw27304step3 raw27304step3Labels := by
      have ha : raw27304step3 = (fun i j => raw27304step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27304step3 raw27304step2; decide +kernel
      have hl : raw27304step3Labels = raw27304step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27304step2 raw27304step2Labels permutation9 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw27305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw27305Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw27305step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27305step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw27305step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27305step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]
def raw27305step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27305step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw27305step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27305 raw27305Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw27305 raw27305Labels = mixedMoment B raw27305step0 raw27305step0Labels := by
      have hz : ∀ j, raw27305 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27305step0 = (fun i j => raw27305 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27305step0 raw27305; decide +kernel
      have hl : raw27305step0Labels = raw27305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27305 raw27305Labels permutation590 hz
    mixedMoment B raw27305step0 raw27305step0Labels = mixedMoment B raw27305step1 raw27305step1Labels := by
      have hz : ∀ j, raw27305step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27305step1 = (fun i j => raw27305step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27305step1 raw27305step0; decide +kernel
      have hl : raw27305step1Labels = raw27305step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27305step0 raw27305step0Labels permutation56 hz
    mixedMoment B raw27305step1 raw27305step1Labels = mixedMoment B raw27305step2 raw27305step2Labels := by
      have hz : ∀ i, raw27305step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27305step2 = (fun i j => raw27305step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27305step2 raw27305step1; decide +kernel
      have hl : raw27305step2Labels = (fun j => raw27305step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27305step1 raw27305step1Labels permutation6 hz
    mixedMoment B raw27305step2 raw27305step2Labels = mixedMoment B raw27305step3 raw27305step3Labels := by
      have ha : raw27305step3 = (fun i j => raw27305step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27305step3 raw27305step2; decide +kernel
      have hl : raw27305step3Labels = raw27305step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27305step2 raw27305step2Labels permutation9 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw27306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw27306Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw27306step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27306step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![2, -2], ![1, -1]]
def raw27306step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27306step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw27306step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27306 raw27306Labels = mixedMoment B node4057 node4057Labels := by
  calc
    mixedMoment B raw27306 raw27306Labels = mixedMoment B raw27306step0 raw27306step0Labels := by
      have hz : ∀ j, raw27306 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27306step0 = (fun i j => raw27306 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27306step0 raw27306; decide +kernel
      have hl : raw27306step0Labels = raw27306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27306 raw27306Labels permutation265 hz
    mixedMoment B raw27306step0 raw27306step0Labels = mixedMoment B raw27306step1 raw27306step1Labels := by
      have hz : ∀ i, raw27306step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27306step1 = (fun i j => raw27306step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27306step1 raw27306step0; decide +kernel
      have hl : raw27306step1Labels = (fun j => raw27306step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27306step0 raw27306step0Labels permutation6 hz
    mixedMoment B raw27306step1 raw27306step1Labels = mixedMoment B raw27306step2 raw27306step2Labels := by
      have ha : raw27306step2 = (fun i j => raw27306step1 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27306step2 raw27306step1; decide +kernel
      have hl : raw27306step2Labels = raw27306step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27306step1 raw27306step1Labels permutation33 permutation0
    _ = mixedMoment B node4057 node4057Labels := by rfl

def raw27307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw27307Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27307step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![2, -2], ![1, -1]]
def raw27307step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27307step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw27307step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27307 raw27307Labels = mixedMoment B node4063 node4063Labels := by
  calc
    mixedMoment B raw27307 raw27307Labels = mixedMoment B raw27307step0 raw27307step0Labels := by
      have hz : ∀ i, raw27307 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27307step0 = (fun i j => raw27307 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27307step0 raw27307; decide +kernel
      have hl : raw27307step0Labels = (fun j => raw27307Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27307 raw27307Labels permutation6 hz
    mixedMoment B raw27307step0 raw27307step0Labels = mixedMoment B raw27307step1 raw27307step1Labels := by
      have ha : raw27307step1 = (fun i j => raw27307step0 (permutation153 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27307step1 raw27307step0; decide +kernel
      have hl : raw27307step1Labels = raw27307step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27307step0 raw27307step0Labels permutation153 permutation0
    _ = mixedMoment B node4063 node4063Labels := by rfl

def raw27308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw27308Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw27308step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27308step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw27308step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27308step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw27308step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27308 raw27308Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw27308 raw27308Labels = mixedMoment B raw27308step0 raw27308step0Labels := by
      have hz : ∀ j, raw27308 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27308step0 = (fun i j => raw27308 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27308step0 raw27308; decide +kernel
      have hl : raw27308step0Labels = raw27308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27308 raw27308Labels permutation590 hz
    mixedMoment B raw27308step0 raw27308step0Labels = mixedMoment B raw27308step1 raw27308step1Labels := by
      have hz : ∀ j, raw27308step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27308step1 = (fun i j => raw27308step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27308step1 raw27308step0; decide +kernel
      have hl : raw27308step1Labels = raw27308step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27308step0 raw27308step0Labels permutation56 hz
    mixedMoment B raw27308step1 raw27308step1Labels = mixedMoment B raw27308step2 raw27308step2Labels := by
      have hz : ∀ i, raw27308step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw27308step2 = (fun i j => raw27308step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw27308step2 raw27308step1; decide +kernel
      have hl : raw27308step2Labels = (fun j => raw27308step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw27308step1 raw27308step1Labels permutation6 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw27309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw27309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw27309step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27309step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def raw27309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27309 raw27309Labels = mixedMoment B node1820 node1820Labels := by
  calc
    mixedMoment B raw27309 raw27309Labels = mixedMoment B raw27309step0 raw27309step0Labels := by
      have hz : ∀ j, raw27309 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27309step0 = (fun i j => raw27309 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27309step0 raw27309; decide +kernel
      have hl : raw27309step0Labels = raw27309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27309 raw27309Labels permutation434 hz
    mixedMoment B raw27309step0 raw27309step0Labels = mixedMoment B raw27309step1 raw27309step1Labels := by
      have hz : ∀ j, raw27309step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27309step1 = (fun i j => raw27309step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27309step1 raw27309step0; decide +kernel
      have hl : raw27309step1Labels = raw27309step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27309step0 raw27309step0Labels permutation80 hz
    _ = mixedMoment B node1820 node1820Labels := by rfl

def raw27310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![3, -3, 0]]
def raw27310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw27310step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27310 raw27310Labels = mixedMoment B node1971 node1971Labels := by
  calc
    mixedMoment B raw27310 raw27310Labels = mixedMoment B raw27310step0 raw27310step0Labels := by
      have hz : ∀ j, raw27310 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27310step0 = (fun i j => raw27310 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27310step0 raw27310; decide +kernel
      have hl : raw27310step0Labels = raw27310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27310 raw27310Labels permutation434 hz
    _ = mixedMoment B node1971 node1971Labels := by rfl

def raw27311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw27311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, 1, -3], ![3, -3, 0]]
def raw27311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27311 raw27311Labels = mixedMoment B node1971 node1971Labels := by
  calc
    mixedMoment B raw27311 raw27311Labels = mixedMoment B raw27311step0 raw27311step0Labels := by
      have hz : ∀ j, raw27311 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27311step0 = (fun i j => raw27311 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27311step0 raw27311; decide +kernel
      have hl : raw27311step0Labels = raw27311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27311 raw27311Labels permutation346 hz
    _ = mixedMoment B node1971 node1971Labels := by rfl

def raw27312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw27312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, 1, -3], ![2, -2, 0]]
def raw27312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27312step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, 1, -3], ![2, -2, 0]]
def raw27312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27312step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw27312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27312 raw27312Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw27312 raw27312Labels = mixedMoment B raw27312step0 raw27312step0Labels := by
      have hz : ∀ j, raw27312 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27312step0 = (fun i j => raw27312 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27312step0 raw27312; decide +kernel
      have hl : raw27312step0Labels = raw27312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27312 raw27312Labels permutation434 hz
    mixedMoment B raw27312step0 raw27312step0Labels = mixedMoment B raw27312step1 raw27312step1Labels := by
      have hz : ∀ j, raw27312step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27312step1 = (fun i j => raw27312step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27312step1 raw27312step0; decide +kernel
      have hl : raw27312step1Labels = raw27312step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27312step0 raw27312step0Labels permutation80 hz
    mixedMoment B raw27312step1 raw27312step1Labels = mixedMoment B raw27312step2 raw27312step2Labels := by
      have ha : raw27312step2 = (fun i j => raw27312step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27312step2 raw27312step1; decide +kernel
      have hl : raw27312step2Labels = raw27312step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27312step1 raw27312step1Labels permutation9 permutation2
    _ = mixedMoment B node2065 node2065Labels := by rfl

def raw27313 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27313Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27313step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27313step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -2, 1], ![-3, 0, 3]]
def raw27313step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27313step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27313step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27313 raw27313Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw27313 raw27313Labels = mixedMoment B raw27313step0 raw27313step0Labels := by
      have hz : ∀ j, raw27313 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27313step0 = (fun i j => raw27313 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27313step0 raw27313; decide +kernel
      have hl : raw27313step0Labels = raw27313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27313 raw27313Labels permutation434 hz
    mixedMoment B raw27313step0 raw27313step0Labels = mixedMoment B raw27313step1 raw27313step1Labels := by
      have hz : ∀ j, raw27313step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27313step1 = (fun i j => raw27313step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27313step1 raw27313step0; decide +kernel
      have hl : raw27313step1Labels = raw27313step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27313step0 raw27313step0Labels permutation80 hz
    mixedMoment B raw27313step1 raw27313step1Labels = mixedMoment B raw27313step2 raw27313step2Labels := by
      have ha : raw27313step2 = (fun i j => raw27313step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27313step2 raw27313step1; decide +kernel
      have hl : raw27313step2Labels = raw27313step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27313step1 raw27313step1Labels permutation31 permutation2
    _ = mixedMoment B node2287 node2287Labels := by rfl

def raw27314 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27314Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27314step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27314step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -2, 1], ![-3, 0, 3]]
def raw27314step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27314step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw27314step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27314 raw27314Labels = mixedMoment B node2282 node2282Labels := by
  calc
    mixedMoment B raw27314 raw27314Labels = mixedMoment B raw27314step0 raw27314step0Labels := by
      have hz : ∀ j, raw27314 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27314step0 = (fun i j => raw27314 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27314step0 raw27314; decide +kernel
      have hl : raw27314step0Labels = raw27314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27314 raw27314Labels permutation434 hz
    mixedMoment B raw27314step0 raw27314step0Labels = mixedMoment B raw27314step1 raw27314step1Labels := by
      have hz : ∀ j, raw27314step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27314step1 = (fun i j => raw27314step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27314step1 raw27314step0; decide +kernel
      have hl : raw27314step1Labels = raw27314step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27314step0 raw27314step0Labels permutation80 hz
    mixedMoment B raw27314step1 raw27314step1Labels = mixedMoment B raw27314step2 raw27314step2Labels := by
      have ha : raw27314step2 = (fun i j => raw27314step1 (permutation27 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27314step2 raw27314step1; decide +kernel
      have hl : raw27314step2Labels = raw27314step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27314step1 raw27314step1Labels permutation27 permutation2
    _ = mixedMoment B node2282 node2282Labels := by rfl

def raw27315 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27315step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw27315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27315step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw27315step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27315 raw27315Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw27315 raw27315Labels = mixedMoment B raw27315step0 raw27315step0Labels := by
      have hz : ∀ j, raw27315 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27315step0 = (fun i j => raw27315 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27315step0 raw27315; decide +kernel
      have hl : raw27315step0Labels = raw27315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27315 raw27315Labels permutation434 hz
    mixedMoment B raw27315step0 raw27315step0Labels = mixedMoment B raw27315step1 raw27315step1Labels := by
      have ha : raw27315step1 = (fun i j => raw27315step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27315step1 raw27315step0; decide +kernel
      have hl : raw27315step1Labels = raw27315step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27315step0 raw27315step0Labels permutation36 permutation4
    mixedMoment B raw27315step1 raw27315step1Labels = mixedMoment B raw27315step2 raw27315step2Labels := by
      have ha : raw27315step2 = -raw27315step1 := by apply Matrix.ext; change ∀ i j, raw27315step2 i j = -(raw27315step1 i j); unfold raw27315step2 raw27315step1; decide +kernel
      have hl : raw27315step2Labels = raw27315step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw27316 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27316step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw27316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27316step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw27316step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27316 raw27316Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw27316 raw27316Labels = mixedMoment B raw27316step0 raw27316step0Labels := by
      have hz : ∀ j, raw27316 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27316step0 = (fun i j => raw27316 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27316step0 raw27316; decide +kernel
      have hl : raw27316step0Labels = raw27316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27316 raw27316Labels permutation346 hz
    mixedMoment B raw27316step0 raw27316step0Labels = mixedMoment B raw27316step1 raw27316step1Labels := by
      have ha : raw27316step1 = (fun i j => raw27316step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27316step1 raw27316step0; decide +kernel
      have hl : raw27316step1Labels = raw27316step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27316step0 raw27316step0Labels permutation36 permutation4
    mixedMoment B raw27316step1 raw27316step1Labels = mixedMoment B raw27316step2 raw27316step2Labels := by
      have ha : raw27316step2 = -raw27316step1 := by apply Matrix.ext; change ∀ i j, raw27316step2 i j = -(raw27316step1 i j); unfold raw27316step2 raw27316step1; decide +kernel
      have hl : raw27316step2Labels = raw27316step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw27317 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27317step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -3, 1], ![-3, 0, 3]]
def raw27317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27317step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-3, 2, 1]]
def raw27317step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27317step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw27317step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27317 raw27317Labels = mixedMoment B node2222 node2222Labels := by
  calc
    mixedMoment B raw27317 raw27317Labels = mixedMoment B raw27317step0 raw27317step0Labels := by
      have hz : ∀ j, raw27317 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27317step0 = (fun i j => raw27317 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27317step0 raw27317; decide +kernel
      have hl : raw27317step0Labels = raw27317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27317 raw27317Labels permutation434 hz
    mixedMoment B raw27317step0 raw27317step0Labels = mixedMoment B raw27317step1 raw27317step1Labels := by
      have hz : ∀ j, raw27317step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27317step1 = (fun i j => raw27317step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27317step1 raw27317step0; decide +kernel
      have hl : raw27317step1Labels = raw27317step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27317step0 raw27317step0Labels permutation80 hz
    mixedMoment B raw27317step1 raw27317step1Labels = mixedMoment B raw27317step2 raw27317step2Labels := by
      have ha : raw27317step2 = (fun i j => raw27317step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27317step2 raw27317step1; decide +kernel
      have hl : raw27317step2Labels = raw27317step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27317step1 raw27317step1Labels permutation9 permutation4
    mixedMoment B raw27317step2 raw27317step2Labels = mixedMoment B raw27317step3 raw27317step3Labels := by
      have ha : raw27317step3 = -raw27317step2 := by apply Matrix.ext; change ∀ i j, raw27317step3 i j = -(raw27317step2 i j); unfold raw27317step3 raw27317step2; decide +kernel
      have hl : raw27317step3Labels = raw27317step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2222 node2222Labels := by rfl

def raw27318 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27318step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27318step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -2, 1], ![-2, -1, 3]]
def raw27318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27318step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw27318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27318step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw27318step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27318 raw27318Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw27318 raw27318Labels = mixedMoment B raw27318step0 raw27318step0Labels := by
      have hz : ∀ j, raw27318 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27318step0 = (fun i j => raw27318 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27318step0 raw27318; decide +kernel
      have hl : raw27318step0Labels = raw27318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27318 raw27318Labels permutation434 hz
    mixedMoment B raw27318step0 raw27318step0Labels = mixedMoment B raw27318step1 raw27318step1Labels := by
      have hz : ∀ j, raw27318step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27318step1 = (fun i j => raw27318step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27318step1 raw27318step0; decide +kernel
      have hl : raw27318step1Labels = raw27318step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27318step0 raw27318step0Labels permutation80 hz
    mixedMoment B raw27318step1 raw27318step1Labels = mixedMoment B raw27318step2 raw27318step2Labels := by
      have ha : raw27318step2 = (fun i j => raw27318step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27318step2 raw27318step1; decide +kernel
      have hl : raw27318step2Labels = raw27318step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27318step1 raw27318step1Labels permutation9 permutation4
    mixedMoment B raw27318step2 raw27318step2Labels = mixedMoment B raw27318step3 raw27318step3Labels := by
      have ha : raw27318step3 = -raw27318step2 := by apply Matrix.ext; change ∀ i j, raw27318step3 i j = -(raw27318step2 i j); unfold raw27318step3 raw27318step2; decide +kernel
      have hl : raw27318step3Labels = raw27318step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2230 node2230Labels := by rfl

def raw27319 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![0, 0], ![0, 0], ![-1, 1], ![-3, 3]]
def raw27319Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27319step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![0, 0], ![-1, 1], ![-3, 3]]
def raw27319step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27319step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-3, 3]]
def raw27319step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27319step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw27319step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27319 raw27319Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw27319 raw27319Labels = mixedMoment B raw27319step0 raw27319step0Labels := by
      have hz : ∀ j, raw27319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27319step0 = (fun i j => raw27319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27319step0 raw27319; decide +kernel
      have hl : raw27319step0Labels = raw27319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27319 raw27319Labels permutation434 hz
    mixedMoment B raw27319step0 raw27319step0Labels = mixedMoment B raw27319step1 raw27319step1Labels := by
      have hz : ∀ j, raw27319step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27319step1 = (fun i j => raw27319step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27319step1 raw27319step0; decide +kernel
      have hl : raw27319step1Labels = raw27319step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27319step0 raw27319step0Labels permutation80 hz
    mixedMoment B raw27319step1 raw27319step1Labels = mixedMoment B raw27319step2 raw27319step2Labels := by
      have ha : raw27319step2 = (fun i j => raw27319step1 (permutation31 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27319step2 raw27319step1; decide +kernel
      have hl : raw27319step2Labels = raw27319step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27319step1 raw27319step1Labels permutation31 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw27320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27320step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27320 raw27320Labels = mixedMoment B node1813 node1813Labels := by
  calc
    mixedMoment B raw27320 raw27320Labels = mixedMoment B raw27320step0 raw27320step0Labels := by
      have hz : ∀ j, raw27320 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27320step0 = (fun i j => raw27320 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27320step0 raw27320; decide +kernel
      have hl : raw27320step0Labels = raw27320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27320 raw27320Labels permutation346 hz
    _ = mixedMoment B node1813 node1813Labels := by rfl

def raw27321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27321 raw27321Labels = mixedMoment B node1965 node1965Labels := by
  calc
    _ = mixedMoment B node1965 node1965Labels := by rfl

def raw27322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27322Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27322step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27322 raw27322Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw27322 raw27322Labels = mixedMoment B raw27322step0 raw27322step0Labels := by
      have hz : ∀ j, raw27322 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27322step0 = (fun i j => raw27322 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27322step0 raw27322; decide +kernel
      have hl : raw27322step0Labels = raw27322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27322 raw27322Labels permutation346 hz
    _ = mixedMoment B node2058 node2058Labels := by rfl

def raw27323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27323 raw27323Labels = mixedMoment B node1797 node1797Labels := by
  calc
    mixedMoment B raw27323 raw27323Labels = mixedMoment B raw27323step0 raw27323step0Labels := by
      have hz : ∀ j, raw27323 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27323step0 = (fun i j => raw27323 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27323step0 raw27323; decide +kernel
      have hl : raw27323step0Labels = raw27323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27323 raw27323Labels permutation346 hz
    _ = mixedMoment B node1797 node1797Labels := by rfl

def raw27324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27324Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27324 raw27324Labels = mixedMoment B node1957 node1957Labels := by
  calc
    _ = mixedMoment B node1957 node1957Labels := by rfl

def raw27325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27325Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw27325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27325 raw27325Labels = mixedMoment B node1980 node1980Labels := by
  calc
    mixedMoment B raw27325 raw27325Labels = mixedMoment B raw27325step0 raw27325step0Labels := by
      have hz : ∀ j, raw27325 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27325step0 = (fun i j => raw27325 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27325step0 raw27325; decide +kernel
      have hl : raw27325step0Labels = raw27325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27325 raw27325Labels permutation346 hz
    _ = mixedMoment B node1980 node1980Labels := by rfl

def raw27326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw27326Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw27326step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw27326step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27326 raw27326Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw27326 raw27326Labels = mixedMoment B raw27326step0 raw27326step0Labels := by
      have hz : ∀ j, raw27326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27326step0 = (fun i j => raw27326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27326step0 raw27326; decide +kernel
      have hl : raw27326step0Labels = raw27326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27326 raw27326Labels permutation346 hz
    mixedMoment B raw27326step0 raw27326step0Labels = mixedMoment B raw27326step1 raw27326step1Labels := by
      have ha : raw27326step1 = (fun i j => raw27326step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27326step1 raw27326step0; decide +kernel
      have hl : raw27326step1Labels = raw27326step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27326step0 raw27326step0Labels permutation33 permutation2
    _ = mixedMoment B node2028 node2028Labels := by rfl

def raw27327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27327Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27327step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27327step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27327step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27327 raw27327Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw27327 raw27327Labels = mixedMoment B raw27327step0 raw27327step0Labels := by
      have hz : ∀ j, raw27327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27327step0 = (fun i j => raw27327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27327step0 raw27327; decide +kernel
      have hl : raw27327step0Labels = raw27327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27327 raw27327Labels permutation346 hz
    mixedMoment B raw27327step0 raw27327step0Labels = mixedMoment B raw27327step1 raw27327step1Labels := by
      have ha : raw27327step1 = (fun i j => raw27327step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27327step1 raw27327step0; decide +kernel
      have hl : raw27327step1Labels = raw27327step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27327step0 raw27327step0Labels permutation149 permutation2
    mixedMoment B raw27327step1 raw27327step1Labels = mixedMoment B raw27327step2 raw27327step2Labels := by
      have ha : raw27327step2 = -raw27327step1 := by apply Matrix.ext; change ∀ i j, raw27327step2 i j = -(raw27327step1 i j); unfold raw27327step2 raw27327step1; decide +kernel
      have hl : raw27327step2Labels = raw27327step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2110 node2110Labels := by rfl

def raw27328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27328Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27328step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27328step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27328step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27328 raw27328Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw27328 raw27328Labels = mixedMoment B raw27328step0 raw27328step0Labels := by
      have hz : ∀ j, raw27328 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27328step0 = (fun i j => raw27328 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27328step0 raw27328; decide +kernel
      have hl : raw27328step0Labels = raw27328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27328 raw27328Labels permutation346 hz
    mixedMoment B raw27328step0 raw27328step0Labels = mixedMoment B raw27328step1 raw27328step1Labels := by
      have ha : raw27328step1 = (fun i j => raw27328step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27328step1 raw27328step0; decide +kernel
      have hl : raw27328step1Labels = raw27328step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27328step0 raw27328step0Labels permutation149 permutation2
    mixedMoment B raw27328step1 raw27328step1Labels = mixedMoment B raw27328step2 raw27328step2Labels := by
      have ha : raw27328step2 = -raw27328step1 := by apply Matrix.ext; change ∀ i j, raw27328step2 i j = -(raw27328step1 i j); unfold raw27328step2 raw27328step1; decide +kernel
      have hl : raw27328step2Labels = raw27328step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2092 node2092Labels := by rfl

def raw27329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27329Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27329step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27329step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27329step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27329step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27329 raw27329Labels = mixedMoment B node1976 node1976Labels := by
  calc
    mixedMoment B raw27329 raw27329Labels = mixedMoment B raw27329step0 raw27329step0Labels := by
      have ha : raw27329step0 = (fun i j => raw27329 (permutation644 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27329step0 raw27329; decide +kernel
      have hl : raw27329step0Labels = raw27329Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27329 raw27329Labels permutation644 permutation2
    mixedMoment B raw27329step0 raw27329step0Labels = mixedMoment B raw27329step1 raw27329step1Labels := by
      have ha : raw27329step1 = -raw27329step0 := by apply Matrix.ext; change ∀ i j, raw27329step1 i j = -(raw27329step0 i j); unfold raw27329step1 raw27329step0; decide +kernel
      have hl : raw27329step1Labels = raw27329step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1976 node1976Labels := by rfl

def raw27330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw27330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27330 raw27330Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw27330 raw27330Labels = mixedMoment B raw27330step0 raw27330step0Labels := by
      have hz : ∀ j, raw27330 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27330step0 = (fun i j => raw27330 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27330step0 raw27330; decide +kernel
      have hl : raw27330step0Labels = raw27330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27330 raw27330Labels permutation346 hz
    mixedMoment B raw27330step0 raw27330step0Labels = mixedMoment B raw27330step1 raw27330step1Labels := by
      have ha : raw27330step1 = (fun i j => raw27330step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27330step1 raw27330step0; decide +kernel
      have hl : raw27330step1Labels = raw27330step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27330step0 raw27330step0Labels permutation151 permutation2
    mixedMoment B raw27330step1 raw27330step1Labels = mixedMoment B raw27330step2 raw27330step2Labels := by
      have ha : raw27330step2 = -raw27330step1 := by apply Matrix.ext; change ∀ i j, raw27330step2 i j = -(raw27330step1 i j); unfold raw27330step2 raw27330step1; decide +kernel
      have hl : raw27330step2Labels = raw27330step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2092 node2092Labels := by rfl

def raw27331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw27331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1], ![3, 0, -3]]
def raw27331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27331step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27331 raw27331Labels = mixedMoment B node1828 node1828Labels := by
  calc
    mixedMoment B raw27331 raw27331Labels = mixedMoment B raw27331step0 raw27331step0Labels := by
      have hz : ∀ j, raw27331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27331step0 = (fun i j => raw27331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27331step0 raw27331; decide +kernel
      have hl : raw27331step0Labels = raw27331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27331 raw27331Labels permutation346 hz
    mixedMoment B raw27331step0 raw27331step0Labels = mixedMoment B raw27331step1 raw27331step1Labels := by
      have ha : raw27331step1 = (fun i j => raw27331step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27331step1 raw27331step0; decide +kernel
      have hl : raw27331step1Labels = raw27331step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27331step0 raw27331step0Labels permutation149 permutation2
    mixedMoment B raw27331step1 raw27331step1Labels = mixedMoment B raw27331step2 raw27331step2Labels := by
      have ha : raw27331step2 = -raw27331step1 := by apply Matrix.ext; change ∀ i j, raw27331step2 i j = -(raw27331step1 i j); unfold raw27331step2 raw27331step1; decide +kernel
      have hl : raw27331step2Labels = raw27331step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1828 node1828Labels := by rfl

def raw27332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![4, -1, -3]]
def raw27332Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![4, -1, -3]]
def raw27332step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27332step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27332step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27332 raw27332Labels = mixedMoment B node949 node949Labels := by
  calc
    mixedMoment B raw27332 raw27332Labels = mixedMoment B raw27332step0 raw27332step0Labels := by
      have hz : ∀ j, raw27332 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27332step0 = (fun i j => raw27332 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27332step0 raw27332; decide +kernel
      have hl : raw27332step0Labels = raw27332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27332 raw27332Labels permutation346 hz
    mixedMoment B raw27332step0 raw27332step0Labels = mixedMoment B raw27332step1 raw27332step1Labels := by
      have ha : raw27332step1 = (fun i j => raw27332step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27332step1 raw27332step0; decide +kernel
      have hl : raw27332step1Labels = raw27332step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27332step0 raw27332step0Labels permutation149 permutation2
    mixedMoment B raw27332step1 raw27332step1Labels = mixedMoment B raw27332step2 raw27332step2Labels := by
      have ha : raw27332step2 = -raw27332step1 := by apply Matrix.ext; change ∀ i j, raw27332step2 i j = -(raw27332step1 i j); unfold raw27332step2 raw27332step1; decide +kernel
      have hl : raw27332step2Labels = raw27332step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node949 node949Labels := by rfl

def raw27333 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![0, 0], ![-1, 1], ![-1, 1], ![3, -3]]
def raw27333Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27333step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw27333step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27333step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw27333step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27333step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw27333step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27333step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw27333step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27333 raw27333Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw27333 raw27333Labels = mixedMoment B raw27333step0 raw27333step0Labels := by
      have hz : ∀ j, raw27333 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27333step0 = (fun i j => raw27333 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27333step0 raw27333; decide +kernel
      have hl : raw27333step0Labels = raw27333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27333 raw27333Labels permutation346 hz
    mixedMoment B raw27333step0 raw27333step0Labels = mixedMoment B raw27333step1 raw27333step1Labels := by
      have hz : ∀ j, raw27333step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw27333step1 = (fun i j => raw27333step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw27333step1 raw27333step0; decide +kernel
      have hl : raw27333step1Labels = raw27333step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27333step0 raw27333step0Labels permutation32 hz
    mixedMoment B raw27333step1 raw27333step1Labels = mixedMoment B raw27333step2 raw27333step2Labels := by
      have ha : raw27333step2 = (fun i j => raw27333step1 (permutation26 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27333step2 raw27333step1; decide +kernel
      have hl : raw27333step2Labels = raw27333step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27333step1 raw27333step1Labels permutation26 permutation0
    mixedMoment B raw27333step2 raw27333step2Labels = mixedMoment B raw27333step3 raw27333step3Labels := by
      have ha : raw27333step3 = -raw27333step2 := by apply Matrix.ext; change ∀ i j, raw27333step3 i j = -(raw27333step2 i j); unfold raw27333step3 raw27333step2; decide +kernel
      have hl : raw27333step3Labels = raw27333step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw27334 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27334Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27334step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw27334step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27334 raw27334Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw27334 raw27334Labels = mixedMoment B raw27334step0 raw27334step0Labels := by
      have hz : ∀ j, raw27334 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27334step0 = (fun i j => raw27334 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27334step0 raw27334; decide +kernel
      have hl : raw27334step0Labels = raw27334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27334 raw27334Labels permutation346 hz
    mixedMoment B raw27334step0 raw27334step0Labels = mixedMoment B raw27334step1 raw27334step1Labels := by
      have ha : raw27334step1 = (fun i j => raw27334step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27334step1 raw27334step0; decide +kernel
      have hl : raw27334step1Labels = raw27334step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27334step0 raw27334step0Labels permutation139 permutation2
    _ = mixedMoment B node2259 node2259Labels := by rfl

def raw27335 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw27335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27335step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw27335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27335 raw27335Labels = mixedMoment B node1930 node1930Labels := by
  calc
    mixedMoment B raw27335 raw27335Labels = mixedMoment B raw27335step0 raw27335step0Labels := by
      have ha : raw27335step0 = (fun i j => raw27335 (permutation170 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27335step0 raw27335; decide +kernel
      have hl : raw27335step0Labels = raw27335Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27335 raw27335Labels permutation170 permutation4
    mixedMoment B raw27335step0 raw27335step0Labels = mixedMoment B raw27335step1 raw27335step1Labels := by
      have ha : raw27335step1 = -raw27335step0 := by apply Matrix.ext; change ∀ i j, raw27335step1 i j = -(raw27335step0 i j); unfold raw27335step1 raw27335step0; decide +kernel
      have hl : raw27335step1Labels = raw27335step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1930 node1930Labels := by rfl

def raw27336 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw27336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -3, 3], ![-2, 2, 0], ![-2, 1, 1]]
def raw27336step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27336step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![2, -2, 0], ![2, -1, -1]]
def raw27336step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27336 raw27336Labels = mixedMoment B node1934 node1934Labels := by
  calc
    mixedMoment B raw27336 raw27336Labels = mixedMoment B raw27336step0 raw27336step0Labels := by
      have hz : ∀ j, raw27336 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27336step0 = (fun i j => raw27336 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27336step0 raw27336; decide +kernel
      have hl : raw27336step0Labels = raw27336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27336 raw27336Labels permutation346 hz
    mixedMoment B raw27336step0 raw27336step0Labels = mixedMoment B raw27336step1 raw27336step1Labels := by
      have ha : raw27336step1 = (fun i j => raw27336step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27336step1 raw27336step0; decide +kernel
      have hl : raw27336step1Labels = raw27336step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27336step0 raw27336step0Labels permutation36 permutation4
    mixedMoment B raw27336step1 raw27336step1Labels = mixedMoment B raw27336step2 raw27336step2Labels := by
      have ha : raw27336step2 = -raw27336step1 := by apply Matrix.ext; change ∀ i j, raw27336step2 i j = -(raw27336step1 i j); unfold raw27336step2 raw27336step1; decide +kernel
      have hl : raw27336step2Labels = raw27336step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1934 node1934Labels := by rfl

def raw27337 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![2, -3, 1], ![-3, 0, 3]]
def raw27337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27337step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -3, 3], ![-1, 1, 0], ![-3, 2, 1]]
def raw27337step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27337step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![3, -2, -1]]
def raw27337step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27337 raw27337Labels = mixedMoment B node1932 node1932Labels := by
  calc
    mixedMoment B raw27337 raw27337Labels = mixedMoment B raw27337step0 raw27337step0Labels := by
      have hz : ∀ j, raw27337 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27337step0 = (fun i j => raw27337 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27337step0 raw27337; decide +kernel
      have hl : raw27337step0Labels = raw27337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27337 raw27337Labels permutation346 hz
    mixedMoment B raw27337step0 raw27337step0Labels = mixedMoment B raw27337step1 raw27337step1Labels := by
      have ha : raw27337step1 = (fun i j => raw27337step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27337step1 raw27337step0; decide +kernel
      have hl : raw27337step1Labels = raw27337step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27337step0 raw27337step0Labels permutation36 permutation4
    mixedMoment B raw27337step1 raw27337step1Labels = mixedMoment B raw27337step2 raw27337step2Labels := by
      have ha : raw27337step2 = -raw27337step1 := by apply Matrix.ext; change ∀ i j, raw27337step2 i j = -(raw27337step1 i j); unfold raw27337step2 raw27337step1; decide +kernel
      have hl : raw27337step2Labels = raw27337step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1932 node1932Labels := by rfl

def raw27338 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw27338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw27338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27338step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw27338step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27338 raw27338Labels = mixedMoment B node1946 node1946Labels := by
  calc
    mixedMoment B raw27338 raw27338Labels = mixedMoment B raw27338step0 raw27338step0Labels := by
      have hz : ∀ j, raw27338 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27338step0 = (fun i j => raw27338 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27338step0 raw27338; decide +kernel
      have hl : raw27338step0Labels = raw27338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27338 raw27338Labels permutation346 hz
    mixedMoment B raw27338step0 raw27338step0Labels = mixedMoment B raw27338step1 raw27338step1Labels := by
      have ha : raw27338step1 = (fun i j => raw27338step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27338step1 raw27338step0; decide +kernel
      have hl : raw27338step1Labels = raw27338step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27338step0 raw27338step0Labels permutation33 permutation4
    mixedMoment B raw27338step1 raw27338step1Labels = mixedMoment B raw27338step2 raw27338step2Labels := by
      have ha : raw27338step2 = -raw27338step1 := by apply Matrix.ext; change ∀ i j, raw27338step2 i j = -(raw27338step1 i j); unfold raw27338step2 raw27338step1; decide +kernel
      have hl : raw27338step2Labels = raw27338step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1946 node1946Labels := by rfl

def raw27339 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27339step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27339 raw27339Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw27339 raw27339Labels = mixedMoment B raw27339step0 raw27339step0Labels := by
      have hz : ∀ j, raw27339 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27339step0 = (fun i j => raw27339 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27339step0 raw27339; decide +kernel
      have hl : raw27339step0Labels = raw27339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27339 raw27339Labels permutation346 hz
    mixedMoment B raw27339step0 raw27339step0Labels = mixedMoment B raw27339step1 raw27339step1Labels := by
      have ha : raw27339step1 = (fun i j => raw27339step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27339step1 raw27339step0; decide +kernel
      have hl : raw27339step1Labels = raw27339step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27339step0 raw27339step0Labels permutation151 permutation2
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw27340 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27340Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw27340step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27340 raw27340Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw27340 raw27340Labels = mixedMoment B raw27340step0 raw27340step0Labels := by
      have hz : ∀ j, raw27340 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27340step0 = (fun i j => raw27340 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27340step0 raw27340; decide +kernel
      have hl : raw27340step0Labels = raw27340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27340 raw27340Labels permutation346 hz
    mixedMoment B raw27340step0 raw27340step0Labels = mixedMoment B raw27340step1 raw27340step1Labels := by
      have ha : raw27340step1 = (fun i j => raw27340step0 (permutation147 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27340step1 raw27340step0; decide +kernel
      have hl : raw27340step1Labels = raw27340step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27340step0 raw27340step0Labels permutation147 permutation2
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw27341 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw27341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27341 raw27341Labels = mixedMoment B node2219 node2219Labels := by
  calc
    mixedMoment B raw27341 raw27341Labels = mixedMoment B raw27341step0 raw27341step0Labels := by
      have ha : raw27341step0 = (fun i j => raw27341 (permutation668 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27341step0 raw27341; decide +kernel
      have hl : raw27341step0Labels = raw27341Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27341 raw27341Labels permutation668 permutation2
    _ = mixedMoment B node2219 node2219Labels := by rfl

def raw27342 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27342Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw27342step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -2, 0]]
def raw27342step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27342 raw27342Labels = mixedMoment B node2221 node2221Labels := by
  calc
    mixedMoment B raw27342 raw27342Labels = mixedMoment B raw27342step0 raw27342step0Labels := by
      have hz : ∀ j, raw27342 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27342step0 = (fun i j => raw27342 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27342step0 raw27342; decide +kernel
      have hl : raw27342step0Labels = raw27342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27342 raw27342Labels permutation346 hz
    mixedMoment B raw27342step0 raw27342step0Labels = mixedMoment B raw27342step1 raw27342step1Labels := by
      have ha : raw27342step1 = (fun i j => raw27342step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27342step1 raw27342step0; decide +kernel
      have hl : raw27342step1Labels = raw27342step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27342step0 raw27342step0Labels permutation146 permutation2
    _ = mixedMoment B node2221 node2221Labels := by rfl

def raw27343 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27343Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27343step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27343step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27343step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27343step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27343 raw27343Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw27343 raw27343Labels = mixedMoment B raw27343step0 raw27343step0Labels := by
      have hz : ∀ j, raw27343 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27343step0 = (fun i j => raw27343 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27343step0 raw27343; decide +kernel
      have hl : raw27343step0Labels = raw27343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27343 raw27343Labels permutation346 hz
    mixedMoment B raw27343step0 raw27343step0Labels = mixedMoment B raw27343step1 raw27343step1Labels := by
      have ha : raw27343step1 = (fun i j => raw27343step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27343step1 raw27343step0; decide +kernel
      have hl : raw27343step1Labels = raw27343step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27343step0 raw27343step0Labels permutation32 permutation4
    mixedMoment B raw27343step1 raw27343step1Labels = mixedMoment B raw27343step2 raw27343step2Labels := by
      have ha : raw27343step2 = -raw27343step1 := by apply Matrix.ext; change ∀ i j, raw27343step2 i j = -(raw27343step1 i j); unfold raw27343step2 raw27343step1; decide +kernel
      have hl : raw27343step2Labels = raw27343step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw27344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27344Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27344step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27344step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27344 raw27344Labels = mixedMoment B node1808 node1808Labels := by
  calc
    mixedMoment B raw27344 raw27344Labels = mixedMoment B raw27344step0 raw27344step0Labels := by
      have hz : ∀ j, raw27344 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27344step0 = (fun i j => raw27344 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27344step0 raw27344; decide +kernel
      have hl : raw27344step0Labels = raw27344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27344 raw27344Labels permutation346 hz
    mixedMoment B raw27344step0 raw27344step0Labels = mixedMoment B raw27344step1 raw27344step1Labels := by
      have ha : raw27344step1 = (fun i j => raw27344step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27344step1 raw27344step0; decide +kernel
      have hl : raw27344step1Labels = raw27344step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27344step0 raw27344step0Labels permutation34 permutation2
    _ = mixedMoment B node1808 node1808Labels := by rfl

def raw27345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27345step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27345 raw27345Labels = mixedMoment B node1961 node1961Labels := by
  calc
    mixedMoment B raw27345 raw27345Labels = mixedMoment B raw27345step0 raw27345step0Labels := by
      have ha : raw27345step0 = (fun i j => raw27345 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27345step0 raw27345; decide +kernel
      have hl : raw27345step0Labels = raw27345Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27345 raw27345Labels permutation154 permutation2
    _ = mixedMoment B node1961 node1961Labels := by rfl

def raw27346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27346Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw27346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27346 raw27346Labels = mixedMoment B node2035 node2035Labels := by
  calc
    mixedMoment B raw27346 raw27346Labels = mixedMoment B raw27346step0 raw27346step0Labels := by
      have hz : ∀ j, raw27346 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27346step0 = (fun i j => raw27346 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27346step0 raw27346; decide +kernel
      have hl : raw27346step0Labels = raw27346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27346 raw27346Labels permutation346 hz
    _ = mixedMoment B node2035 node2035Labels := by rfl

def raw27347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![3, -2, -1]]
def raw27347Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27347step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw27347step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27347 raw27347Labels = mixedMoment B node2062 node2062Labels := by
  calc
    mixedMoment B raw27347 raw27347Labels = mixedMoment B raw27347step0 raw27347step0Labels := by
      have hz : ∀ j, raw27347 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27347step0 = (fun i j => raw27347 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27347step0 raw27347; decide +kernel
      have hl : raw27347step0Labels = raw27347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27347 raw27347Labels permutation520 hz
    mixedMoment B raw27347step0 raw27347step0Labels = mixedMoment B raw27347step1 raw27347step1Labels := by
      have hz : ∀ j, raw27347step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw27347step1 = (fun i j => raw27347step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw27347step1 raw27347step0; decide +kernel
      have hl : raw27347step1Labels = raw27347step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27347step0 raw27347step0Labels permutation80 hz
    _ = mixedMoment B node2062 node2062Labels := by rfl

def raw27348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw27348Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw27348step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw27348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27348 raw27348Labels = mixedMoment B node2054 node2054Labels := by
  calc
    mixedMoment B raw27348 raw27348Labels = mixedMoment B raw27348step0 raw27348step0Labels := by
      have hz : ∀ j, raw27348 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27348step0 = (fun i j => raw27348 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27348step0 raw27348; decide +kernel
      have hl : raw27348step0Labels = raw27348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27348 raw27348Labels permutation346 hz
    mixedMoment B raw27348step0 raw27348step0Labels = mixedMoment B raw27348step1 raw27348step1Labels := by
      have ha : raw27348step1 = (fun i j => raw27348step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27348step1 raw27348step0; decide +kernel
      have hl : raw27348step1Labels = raw27348step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27348step0 raw27348step0Labels permutation34 permutation2
    _ = mixedMoment B node2054 node2054Labels := by rfl

def raw27349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw27349Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw27349step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw27349step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27349step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27349step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27349 raw27349Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw27349 raw27349Labels = mixedMoment B raw27349step0 raw27349step0Labels := by
      have hz : ∀ j, raw27349 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27349step0 = (fun i j => raw27349 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27349step0 raw27349; decide +kernel
      have hl : raw27349step0Labels = raw27349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27349 raw27349Labels permutation346 hz
    mixedMoment B raw27349step0 raw27349step0Labels = mixedMoment B raw27349step1 raw27349step1Labels := by
      have ha : raw27349step1 = (fun i j => raw27349step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27349step1 raw27349step0; decide +kernel
      have hl : raw27349step1Labels = raw27349step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27349step0 raw27349step0Labels permutation149 permutation2
    mixedMoment B raw27349step1 raw27349step1Labels = mixedMoment B raw27349step2 raw27349step2Labels := by
      have ha : raw27349step2 = -raw27349step1 := by apply Matrix.ext; change ∀ i j, raw27349step2 i j = -(raw27349step1 i j); unfold raw27349step2 raw27349step1; decide +kernel
      have hl : raw27349step2Labels = raw27349step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw27350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw27350Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw27350step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw27350step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27350step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27350 raw27350Labels = mixedMoment B node2486 node2486Labels := by
  calc
    mixedMoment B raw27350 raw27350Labels = mixedMoment B raw27350step0 raw27350step0Labels := by
      have hz : ∀ j, raw27350 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27350step0 = (fun i j => raw27350 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27350step0 raw27350; decide +kernel
      have hl : raw27350step0Labels = raw27350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27350 raw27350Labels permutation346 hz
    mixedMoment B raw27350step0 raw27350step0Labels = mixedMoment B raw27350step1 raw27350step1Labels := by
      have ha : raw27350step1 = (fun i j => raw27350step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27350step1 raw27350step0; decide +kernel
      have hl : raw27350step1Labels = raw27350step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27350step0 raw27350step0Labels permutation149 permutation2
    mixedMoment B raw27350step1 raw27350step1Labels = mixedMoment B raw27350step2 raw27350step2Labels := by
      have ha : raw27350step2 = -raw27350step1 := by apply Matrix.ext; change ∀ i j, raw27350step2 i j = -(raw27350step1 i j); unfold raw27350step2 raw27350step1; decide +kernel
      have hl : raw27350step2Labels = raw27350step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2486 node2486Labels := by rfl

def raw27351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw27351Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw27351step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27351step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27351 raw27351Labels = mixedMoment B node2430 node2430Labels := by
  calc
    mixedMoment B raw27351 raw27351Labels = mixedMoment B raw27351step0 raw27351step0Labels := by
      have ha : raw27351step0 = (fun i j => raw27351 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27351step0 raw27351; decide +kernel
      have hl : raw27351step0Labels = raw27351Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27351 raw27351Labels permutation680 permutation2
    mixedMoment B raw27351step0 raw27351step0Labels = mixedMoment B raw27351step1 raw27351step1Labels := by
      have ha : raw27351step1 = -raw27351step0 := by apply Matrix.ext; change ∀ i j, raw27351step1 i j = -(raw27351step0 i j); unfold raw27351step1 raw27351step0; decide +kernel
      have hl : raw27351step1Labels = raw27351step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2430 node2430Labels := by rfl

def raw27352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw27352Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw27352step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw27352step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27352step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw27352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27352 raw27352Labels = mixedMoment B node2497 node2497Labels := by
  calc
    mixedMoment B raw27352 raw27352Labels = mixedMoment B raw27352step0 raw27352step0Labels := by
      have hz : ∀ j, raw27352 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27352step0 = (fun i j => raw27352 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27352step0 raw27352; decide +kernel
      have hl : raw27352step0Labels = raw27352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27352 raw27352Labels permutation346 hz
    mixedMoment B raw27352step0 raw27352step0Labels = mixedMoment B raw27352step1 raw27352step1Labels := by
      have ha : raw27352step1 = (fun i j => raw27352step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27352step1 raw27352step0; decide +kernel
      have hl : raw27352step1Labels = raw27352step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27352step0 raw27352step0Labels permutation151 permutation2
    mixedMoment B raw27352step1 raw27352step1Labels = mixedMoment B raw27352step2 raw27352step2Labels := by
      have ha : raw27352step2 = -raw27352step1 := by apply Matrix.ext; change ∀ i j, raw27352step2 i j = -(raw27352step1 i j); unfold raw27352step2 raw27352step1; decide +kernel
      have hl : raw27352step2Labels = raw27352step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2497 node2497Labels := by rfl

def raw27353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw27353Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, -1, 2], ![2, -1, -1], ![3, -1, -2]]
def raw27353step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw27353step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27353step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27353step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27353 raw27353Labels = mixedMoment B node2340 node2340Labels := by
  calc
    mixedMoment B raw27353 raw27353Labels = mixedMoment B raw27353step0 raw27353step0Labels := by
      have hz : ∀ j, raw27353 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27353step0 = (fun i j => raw27353 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27353step0 raw27353; decide +kernel
      have hl : raw27353step0Labels = raw27353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27353 raw27353Labels permutation346 hz
    mixedMoment B raw27353step0 raw27353step0Labels = mixedMoment B raw27353step1 raw27353step1Labels := by
      have ha : raw27353step1 = (fun i j => raw27353step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27353step1 raw27353step0; decide +kernel
      have hl : raw27353step1Labels = raw27353step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27353step0 raw27353step0Labels permutation149 permutation2
    mixedMoment B raw27353step1 raw27353step1Labels = mixedMoment B raw27353step2 raw27353step2Labels := by
      have ha : raw27353step2 = -raw27353step1 := by apply Matrix.ext; change ∀ i j, raw27353step2 i j = -(raw27353step1 i j); unfold raw27353step2 raw27353step1; decide +kernel
      have hl : raw27353step2Labels = raw27353step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2340 node2340Labels := by rfl

def raw27354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![4, -2, -2]]
def raw27354Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![4, -2, -2]]
def raw27354step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw27354step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27354step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw27354step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27354 raw27354Labels = mixedMoment B node1137 node1137Labels := by
  calc
    mixedMoment B raw27354 raw27354Labels = mixedMoment B raw27354step0 raw27354step0Labels := by
      have hz : ∀ j, raw27354 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27354step0 = (fun i j => raw27354 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27354step0 raw27354; decide +kernel
      have hl : raw27354step0Labels = raw27354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27354 raw27354Labels permutation346 hz
    mixedMoment B raw27354step0 raw27354step0Labels = mixedMoment B raw27354step1 raw27354step1Labels := by
      have ha : raw27354step1 = (fun i j => raw27354step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27354step1 raw27354step0; decide +kernel
      have hl : raw27354step1Labels = raw27354step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27354step0 raw27354step0Labels permutation149 permutation2
    mixedMoment B raw27354step1 raw27354step1Labels = mixedMoment B raw27354step2 raw27354step2Labels := by
      have ha : raw27354step2 = -raw27354step1 := by apply Matrix.ext; change ∀ i j, raw27354step2 i j = -(raw27354step1 i j); unfold raw27354step2 raw27354step1; decide +kernel
      have hl : raw27354step2Labels = raw27354step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1137 node1137Labels := by rfl

def raw27355 : Matrix (Fin 6) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![0, 0], ![-2, 2], ![1, -1], ![2, -2]]
def raw27355Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27355step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw27355step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27355step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw27355step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27355step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw27355step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27355 raw27355Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw27355 raw27355Labels = mixedMoment B raw27355step0 raw27355step0Labels := by
      have hz : ∀ j, raw27355 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27355step0 = (fun i j => raw27355 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27355step0 raw27355; decide +kernel
      have hl : raw27355step0Labels = raw27355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27355 raw27355Labels permutation346 hz
    mixedMoment B raw27355step0 raw27355step0Labels = mixedMoment B raw27355step1 raw27355step1Labels := by
      have hz : ∀ j, raw27355step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw27355step1 = (fun i j => raw27355step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw27355step1 raw27355step0; decide +kernel
      have hl : raw27355step1Labels = raw27355step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27355step0 raw27355step0Labels permutation32 hz
    mixedMoment B raw27355step1 raw27355step1Labels = mixedMoment B raw27355step2 raw27355step2Labels := by
      have ha : raw27355step2 = (fun i j => raw27355step1 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27355step2 raw27355step1; decide +kernel
      have hl : raw27355step2Labels = raw27355step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27355step1 raw27355step1Labels permutation14 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw27356 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27356Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27356step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw27356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27356step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw27356step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27356 raw27356Labels = mixedMoment B node2207 node2207Labels := by
  calc
    mixedMoment B raw27356 raw27356Labels = mixedMoment B raw27356step0 raw27356step0Labels := by
      have hz : ∀ j, raw27356 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27356step0 = (fun i j => raw27356 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27356step0 raw27356; decide +kernel
      have hl : raw27356step0Labels = raw27356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27356 raw27356Labels permutation346 hz
    mixedMoment B raw27356step0 raw27356step0Labels = mixedMoment B raw27356step1 raw27356step1Labels := by
      have ha : raw27356step1 = (fun i j => raw27356step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27356step1 raw27356step0; decide +kernel
      have hl : raw27356step1Labels = raw27356step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27356step0 raw27356step0Labels permutation35 permutation4
    mixedMoment B raw27356step1 raw27356step1Labels = mixedMoment B raw27356step2 raw27356step2Labels := by
      have ha : raw27356step2 = -raw27356step1 := by apply Matrix.ext; change ∀ i j, raw27356step2 i j = -(raw27356step1 i j); unfold raw27356step2 raw27356step1; decide +kernel
      have hl : raw27356step2Labels = raw27356step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2207 node2207Labels := by rfl

def raw27357 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27357Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27357step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw27357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27357 raw27357Labels = mixedMoment B node3472 node3472Labels := by
  calc
    mixedMoment B raw27357 raw27357Labels = mixedMoment B raw27357step0 raw27357step0Labels := by
      have hz : ∀ j, raw27357 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27357step0 = (fun i j => raw27357 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27357step0 raw27357; decide +kernel
      have hl : raw27357step0Labels = raw27357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27357 raw27357Labels permutation346 hz
    mixedMoment B raw27357step0 raw27357step0Labels = mixedMoment B raw27357step1 raw27357step1Labels := by
      have ha : raw27357step1 = (fun i j => raw27357step0 (permutation148 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27357step1 raw27357step0; decide +kernel
      have hl : raw27357step1Labels = raw27357step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27357step0 raw27357step0Labels permutation148 permutation2
    _ = mixedMoment B node3472 node3472Labels := by rfl

def raw27358 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27358Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27358step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw27358step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27358 raw27358Labels = mixedMoment B node3437 node3437Labels := by
  calc
    mixedMoment B raw27358 raw27358Labels = mixedMoment B raw27358step0 raw27358step0Labels := by
      have ha : raw27358step0 = (fun i j => raw27358 (permutation679 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27358step0 raw27358; decide +kernel
      have hl : raw27358step0Labels = raw27358Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27358 raw27358Labels permutation679 permutation2
    _ = mixedMoment B node3437 node3437Labels := by rfl

def raw27359 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27359Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27359step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27359step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27359 raw27359Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw27359 raw27359Labels = mixedMoment B raw27359step0 raw27359step0Labels := by
      have hz : ∀ j, raw27359 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27359step0 = (fun i j => raw27359 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27359step0 raw27359; decide +kernel
      have hl : raw27359step0Labels = raw27359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27359 raw27359Labels permutation346 hz
    mixedMoment B raw27359step0 raw27359step0Labels = mixedMoment B raw27359step1 raw27359step1Labels := by
      have ha : raw27359step1 = (fun i j => raw27359step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27359step1 raw27359step0; decide +kernel
      have hl : raw27359step1Labels = raw27359step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27359step0 raw27359step0Labels permutation151 permutation2
    _ = mixedMoment B node3481 node3481Labels := by rfl

def raw27360 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27360Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw27360step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27360 raw27360Labels = mixedMoment B node3358 node3358Labels := by
  calc
    mixedMoment B raw27360 raw27360Labels = mixedMoment B raw27360step0 raw27360step0Labels := by
      have hz : ∀ j, raw27360 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27360step0 = (fun i j => raw27360 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27360step0 raw27360; decide +kernel
      have hl : raw27360step0Labels = raw27360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27360 raw27360Labels permutation346 hz
    mixedMoment B raw27360step0 raw27360step0Labels = mixedMoment B raw27360step1 raw27360step1Labels := by
      have ha : raw27360step1 = (fun i j => raw27360step0 (permutation148 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27360step1 raw27360step0; decide +kernel
      have hl : raw27360step1Labels = raw27360step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27360step0 raw27360step0Labels permutation148 permutation2
    _ = mixedMoment B node3358 node3358Labels := by rfl

def raw27361 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27361Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw27361step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27361 raw27361Labels = mixedMoment B node1948 node1948Labels := by
  calc
    mixedMoment B raw27361 raw27361Labels = mixedMoment B raw27361step0 raw27361step0Labels := by
      have hz : ∀ j, raw27361 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27361step0 = (fun i j => raw27361 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27361step0 raw27361; decide +kernel
      have hl : raw27361step0Labels = raw27361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27361 raw27361Labels permutation346 hz
    mixedMoment B raw27361step0 raw27361step0Labels = mixedMoment B raw27361step1 raw27361step1Labels := by
      have ha : raw27361step1 = (fun i j => raw27361step0 (permutation148 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27361step1 raw27361step0; decide +kernel
      have hl : raw27361step1Labels = raw27361step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27361step0 raw27361step0Labels permutation148 permutation2
    _ = mixedMoment B node1948 node1948Labels := by rfl

def raw27362 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27362Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw27362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27362step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw27362step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27362 raw27362Labels = mixedMoment B node1910 node1910Labels := by
  calc
    mixedMoment B raw27362 raw27362Labels = mixedMoment B raw27362step0 raw27362step0Labels := by
      have ha : raw27362step0 = (fun i j => raw27362 (permutation165 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27362step0 raw27362; decide +kernel
      have hl : raw27362step0Labels = raw27362Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27362 raw27362Labels permutation165 permutation4
    mixedMoment B raw27362step0 raw27362step0Labels = mixedMoment B raw27362step1 raw27362step1Labels := by
      have ha : raw27362step1 = -raw27362step0 := by apply Matrix.ext; change ∀ i j, raw27362step1 i j = -(raw27362step0 i j); unfold raw27362step1 raw27362step0; decide +kernel
      have hl : raw27362step1Labels = raw27362step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1910 node1910Labels := by rfl

def raw27363 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27363Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![3, -3, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-3, 3, 0]]
def raw27363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def raw27363step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27363 raw27363Labels = mixedMoment B node1916 node1916Labels := by
  calc
    mixedMoment B raw27363 raw27363Labels = mixedMoment B raw27363step0 raw27363step0Labels := by
      have hz : ∀ j, raw27363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27363step0 = (fun i j => raw27363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27363step0 raw27363; decide +kernel
      have hl : raw27363step0Labels = raw27363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27363 raw27363Labels permutation346 hz
    mixedMoment B raw27363step0 raw27363step0Labels = mixedMoment B raw27363step1 raw27363step1Labels := by
      have ha : raw27363step1 = (fun i j => raw27363step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27363step1 raw27363step0; decide +kernel
      have hl : raw27363step1Labels = raw27363step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27363step0 raw27363step0Labels permutation35 permutation4
    mixedMoment B raw27363step1 raw27363step1Labels = mixedMoment B raw27363step2 raw27363step2Labels := by
      have ha : raw27363step2 = -raw27363step1 := by apply Matrix.ext; change ∀ i j, raw27363step2 i j = -(raw27363step1 i j); unfold raw27363step2 raw27363step1; decide +kernel
      have hl : raw27363step2Labels = raw27363step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1916 node1916Labels := by rfl

def raw27364 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw27364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27364step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw27364step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27364 raw27364Labels = mixedMoment B node1948 node1948Labels := by
  calc
    mixedMoment B raw27364 raw27364Labels = mixedMoment B raw27364step0 raw27364step0Labels := by
      have hz : ∀ j, raw27364 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27364step0 = (fun i j => raw27364 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27364step0 raw27364; decide +kernel
      have hl : raw27364step0Labels = raw27364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27364 raw27364Labels permutation346 hz
    mixedMoment B raw27364step0 raw27364step0Labels = mixedMoment B raw27364step1 raw27364step1Labels := by
      have ha : raw27364step1 = (fun i j => raw27364step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27364step1 raw27364step0; decide +kernel
      have hl : raw27364step1Labels = raw27364step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27364step0 raw27364step0Labels permutation35 permutation4
    mixedMoment B raw27364step1 raw27364step1Labels = mixedMoment B raw27364step2 raw27364step2Labels := by
      have ha : raw27364step2 = -raw27364step1 := by apply Matrix.ext; change ∀ i j, raw27364step2 i j = -(raw27364step1 i j); unfold raw27364step2 raw27364step1; decide +kernel
      have hl : raw27364step2Labels = raw27364step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1948 node1948Labels := by rfl

def raw27365 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27365Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27365step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw27365step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27365step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw27365step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27365 raw27365Labels = mixedMoment B node1917 node1917Labels := by
  calc
    mixedMoment B raw27365 raw27365Labels = mixedMoment B raw27365step0 raw27365step0Labels := by
      have hz : ∀ j, raw27365 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27365step0 = (fun i j => raw27365 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27365step0 raw27365; decide +kernel
      have hl : raw27365step0Labels = raw27365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27365 raw27365Labels permutation346 hz
    mixedMoment B raw27365step0 raw27365step0Labels = mixedMoment B raw27365step1 raw27365step1Labels := by
      have ha : raw27365step1 = (fun i j => raw27365step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27365step1 raw27365step0; decide +kernel
      have hl : raw27365step1Labels = raw27365step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27365step0 raw27365step0Labels permutation34 permutation4
    mixedMoment B raw27365step1 raw27365step1Labels = mixedMoment B raw27365step2 raw27365step2Labels := by
      have ha : raw27365step2 = -raw27365step1 := by apply Matrix.ext; change ∀ i j, raw27365step2 i j = -(raw27365step1 i j); unfold raw27365step2 raw27365step1; decide +kernel
      have hl : raw27365step2Labels = raw27365step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1917 node1917Labels := by rfl

def raw27366 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27366step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -2, 3]]
def raw27366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27366step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw27366step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27366 raw27366Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw27366 raw27366Labels = mixedMoment B raw27366step0 raw27366step0Labels := by
      have hz : ∀ j, raw27366 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27366step0 = (fun i j => raw27366 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27366step0 raw27366; decide +kernel
      have hl : raw27366step0Labels = raw27366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27366 raw27366Labels permutation346 hz
    mixedMoment B raw27366step0 raw27366step0Labels = mixedMoment B raw27366step1 raw27366step1Labels := by
      have ha : raw27366step1 = (fun i j => raw27366step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27366step1 raw27366step0; decide +kernel
      have hl : raw27366step1Labels = raw27366step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27366step0 raw27366step0Labels permutation44 permutation4
    mixedMoment B raw27366step1 raw27366step1Labels = mixedMoment B raw27366step2 raw27366step2Labels := by
      have ha : raw27366step2 = -raw27366step1 := by apply Matrix.ext; change ∀ i j, raw27366step2 i j = -(raw27366step1 i j); unfold raw27366step2 raw27366step1; decide +kernel
      have hl : raw27366step2Labels = raw27366step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2259 node2259Labels := by rfl

def raw27367 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw27367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27367step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27367 raw27367Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw27367 raw27367Labels = mixedMoment B raw27367step0 raw27367step0Labels := by
      have ha : raw27367step0 = (fun i j => raw27367 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27367step0 raw27367; decide +kernel
      have hl : raw27367step0Labels = raw27367Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27367 raw27367Labels permutation164 permutation4
    mixedMoment B raw27367step0 raw27367step0Labels = mixedMoment B raw27367step1 raw27367step1Labels := by
      have ha : raw27367step1 = -raw27367step0 := by apply Matrix.ext; change ∀ i j, raw27367step1 i j = -(raw27367step0 i j); unfold raw27367step1 raw27367step0; decide +kernel
      have hl : raw27367step1Labels = raw27367step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2201 node2201Labels := by rfl

def raw27368 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27368Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw27368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27368step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw27368step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27368 raw27368Labels = mixedMoment B node2203 node2203Labels := by
  calc
    mixedMoment B raw27368 raw27368Labels = mixedMoment B raw27368step0 raw27368step0Labels := by
      have hz : ∀ j, raw27368 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw27368step0 = (fun i j => raw27368 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw27368step0 raw27368; decide +kernel
      have hl : raw27368step0Labels = raw27368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27368 raw27368Labels permutation346 hz
    mixedMoment B raw27368step0 raw27368step0Labels = mixedMoment B raw27368step1 raw27368step1Labels := by
      have ha : raw27368step1 = (fun i j => raw27368step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27368step1 raw27368step0; decide +kernel
      have hl : raw27368step1Labels = raw27368step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27368step0 raw27368step0Labels permutation34 permutation4
    mixedMoment B raw27368step1 raw27368step1Labels = mixedMoment B raw27368step2 raw27368step2Labels := by
      have ha : raw27368step2 = -raw27368step1 := by apply Matrix.ext; change ∀ i j, raw27368step2 i j = -(raw27368step1 i j); unfold raw27368step2 raw27368step1; decide +kernel
      have hl : raw27368step2Labels = raw27368step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2203 node2203Labels := by rfl

def raw27369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27369Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27369 raw27369Labels = mixedMoment B node1790 node1790Labels := by
  calc
    mixedMoment B raw27369 raw27369Labels = mixedMoment B raw27369step0 raw27369step0Labels := by
      have ha : raw27369step0 = (fun i j => raw27369 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27369step0 raw27369; decide +kernel
      have hl : raw27369step0Labels = raw27369Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27369 raw27369Labels permutation160 permutation2
    _ = mixedMoment B node1790 node1790Labels := by rfl

def raw27370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27370Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27370 raw27370Labels = mixedMoment B node2009 node2009Labels := by
  calc
    _ = mixedMoment B node2009 node2009Labels := by rfl

def raw27371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw27371Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw27371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27371 raw27371Labels = mixedMoment B node1973 node1973Labels := by
  calc
    mixedMoment B raw27371 raw27371Labels = mixedMoment B raw27371step0 raw27371step0Labels := by
      have ha : raw27371step0 = (fun i j => raw27371 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27371step0 raw27371; decide +kernel
      have hl : raw27371step0Labels = raw27371Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27371 raw27371Labels permutation160 permutation2
    _ = mixedMoment B node1973 node1973Labels := by rfl

def raw27372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw27372Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw27372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw27372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27372 raw27372Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw27372 raw27372Labels = mixedMoment B raw27372step0 raw27372step0Labels := by
      have hz : ∀ j, raw27372 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27372step0 = (fun i j => raw27372 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27372step0 raw27372; decide +kernel
      have hl : raw27372step0Labels = raw27372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27372 raw27372Labels permutation520 hz
    mixedMoment B raw27372step0 raw27372step0Labels = mixedMoment B raw27372step1 raw27372step1Labels := by
      have ha : raw27372step1 = (fun i j => raw27372step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27372step1 raw27372step0; decide +kernel
      have hl : raw27372step1Labels = raw27372step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27372step0 raw27372step0Labels permutation34 permutation2
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw27373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw27373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27373 raw27373Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw27373 raw27373Labels = mixedMoment B raw27373step0 raw27373step0Labels := by
      have ha : raw27373step0 = (fun i j => raw27373 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27373step0 raw27373; decide +kernel
      have hl : raw27373step0Labels = raw27373Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27373 raw27373Labels permutation160 permutation2
    _ = mixedMoment B node2020 node2020Labels := by rfl

def raw27374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27374step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27374 raw27374Labels = mixedMoment B node2483 node2483Labels := by
  calc
    mixedMoment B raw27374 raw27374Labels = mixedMoment B raw27374step0 raw27374step0Labels := by
      have ha : raw27374step0 = (fun i j => raw27374 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27374step0 raw27374; decide +kernel
      have hl : raw27374step0Labels = raw27374Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27374 raw27374Labels permutation686 permutation2
    mixedMoment B raw27374step0 raw27374step0Labels = mixedMoment B raw27374step1 raw27374step1Labels := by
      have ha : raw27374step1 = -raw27374step0 := by apply Matrix.ext; change ∀ i j, raw27374step1 i j = -(raw27374step0 i j); unfold raw27374step1 raw27374step0; decide +kernel
      have hl : raw27374step1Labels = raw27374step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2483 node2483Labels := by rfl

def raw27375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw27375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27375step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27375step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27375 raw27375Labels = mixedMoment B node2440 node2440Labels := by
  calc
    mixedMoment B raw27375 raw27375Labels = mixedMoment B raw27375step0 raw27375step0Labels := by
      have ha : raw27375step0 = (fun i j => raw27375 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27375step0 raw27375; decide +kernel
      have hl : raw27375step0Labels = raw27375Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27375 raw27375Labels permutation686 permutation2
    mixedMoment B raw27375step0 raw27375step0Labels = mixedMoment B raw27375step1 raw27375step1Labels := by
      have ha : raw27375step1 = -raw27375step0 := by apply Matrix.ext; change ∀ i j, raw27375step1 i j = -(raw27375step0 i j); unfold raw27375step1 raw27375step0; decide +kernel
      have hl : raw27375step1Labels = raw27375step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2440 node2440Labels := by rfl

def raw27376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw27376Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27376step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27376step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27376 raw27376Labels = mixedMoment B node2323 node2323Labels := by
  calc
    mixedMoment B raw27376 raw27376Labels = mixedMoment B raw27376step0 raw27376step0Labels := by
      have ha : raw27376step0 = (fun i j => raw27376 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27376step0 raw27376; decide +kernel
      have hl : raw27376step0Labels = raw27376Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27376 raw27376Labels permutation686 permutation2
    mixedMoment B raw27376step0 raw27376step0Labels = mixedMoment B raw27376step1 raw27376step1Labels := by
      have ha : raw27376step1 = -raw27376step0 := by apply Matrix.ext; change ∀ i j, raw27376step1 i j = -(raw27376step0 i j); unfold raw27376step1 raw27376step0; decide +kernel
      have hl : raw27376step1Labels = raw27376step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2323 node2323Labels := by rfl

def raw27377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![4, -2, -2]]
def raw27377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -2, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw27377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27377 raw27377Labels = mixedMoment B node1116 node1116Labels := by
  calc
    mixedMoment B raw27377 raw27377Labels = mixedMoment B raw27377step0 raw27377step0Labels := by
      have ha : raw27377step0 = (fun i j => raw27377 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27377step0 raw27377; decide +kernel
      have hl : raw27377step0Labels = raw27377Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27377 raw27377Labels permutation686 permutation2
    mixedMoment B raw27377step0 raw27377step0Labels = mixedMoment B raw27377step1 raw27377step1Labels := by
      have ha : raw27377step1 = -raw27377step0 := by apply Matrix.ext; change ∀ i j, raw27377step1 i j = -(raw27377step0 i j); unfold raw27377step1 raw27377step0; decide +kernel
      have hl : raw27377step1Labels = raw27377step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1116 node1116Labels := by rfl

def raw27378 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw27378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27378 raw27378Labels = mixedMoment B node3466 node3466Labels := by
  calc
    mixedMoment B raw27378 raw27378Labels = mixedMoment B raw27378step0 raw27378step0Labels := by
      have ha : raw27378step0 = (fun i j => raw27378 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27378step0 raw27378; decide +kernel
      have hl : raw27378step0Labels = raw27378Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27378 raw27378Labels permutation674 permutation2
    _ = mixedMoment B node3466 node3466Labels := by rfl

def raw27379 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27379Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27379step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27379step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27379 raw27379Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw27379 raw27379Labels = mixedMoment B raw27379step0 raw27379step0Labels := by
      have hz : ∀ j, raw27379 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27379step0 = (fun i j => raw27379 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27379step0 raw27379; decide +kernel
      have hl : raw27379step0Labels = raw27379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27379 raw27379Labels permutation434 hz
    mixedMoment B raw27379step0 raw27379step0Labels = mixedMoment B raw27379step1 raw27379step1Labels := by
      have ha : raw27379step1 = (fun i j => raw27379step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27379step1 raw27379step0; decide +kernel
      have hl : raw27379step1Labels = raw27379step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27379step0 raw27379step0Labels permutation151 permutation2
    _ = mixedMoment B node3481 node3481Labels := by rfl

def raw27380 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw27380Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27380 raw27380Labels = mixedMoment B node3350 node3350Labels := by
  calc
    mixedMoment B raw27380 raw27380Labels = mixedMoment B raw27380step0 raw27380step0Labels := by
      have ha : raw27380step0 = (fun i j => raw27380 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27380step0 raw27380; decide +kernel
      have hl : raw27380step0Labels = raw27380Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27380 raw27380Labels permutation682 permutation2
    _ = mixedMoment B node3350 node3350Labels := by rfl

def raw27381 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw27381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27381 raw27381Labels = mixedMoment B node1940 node1940Labels := by
  calc
    mixedMoment B raw27381 raw27381Labels = mixedMoment B raw27381step0 raw27381step0Labels := by
      have ha : raw27381step0 = (fun i j => raw27381 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27381step0 raw27381; decide +kernel
      have hl : raw27381step0Labels = raw27381Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27381 raw27381Labels permutation682 permutation2
    _ = mixedMoment B node1940 node1940Labels := by rfl

def raw27382 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw27382Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw27382step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27382step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw27382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27382 raw27382Labels = mixedMoment B node1910 node1910Labels := by
  calc
    mixedMoment B raw27382 raw27382Labels = mixedMoment B raw27382step0 raw27382step0Labels := by
      have ha : raw27382step0 = (fun i j => raw27382 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27382step0 raw27382; decide +kernel
      have hl : raw27382step0Labels = raw27382Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27382 raw27382Labels permutation167 permutation4
    mixedMoment B raw27382step0 raw27382step0Labels = mixedMoment B raw27382step1 raw27382step1Labels := by
      have ha : raw27382step1 = -raw27382step0 := by apply Matrix.ext; change ∀ i j, raw27382step1 i j = -(raw27382step0 i j); unfold raw27382step1 raw27382step0; decide +kernel
      have hl : raw27382step1Labels = raw27382step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1910 node1910Labels := by rfl

def raw27383 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw27383Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27383step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27383 raw27383Labels = mixedMoment B node1940 node1940Labels := by
  calc
    mixedMoment B raw27383 raw27383Labels = mixedMoment B raw27383step0 raw27383step0Labels := by
      have ha : raw27383step0 = (fun i j => raw27383 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27383step0 raw27383; decide +kernel
      have hl : raw27383step0Labels = raw27383Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27383 raw27383Labels permutation152 permutation4
    mixedMoment B raw27383step0 raw27383step0Labels = mixedMoment B raw27383step1 raw27383step1Labels := by
      have ha : raw27383step1 = -raw27383step0 := by apply Matrix.ext; change ∀ i j, raw27383step1 i j = -(raw27383step0 i j); unfold raw27383step1 raw27383step0; decide +kernel
      have hl : raw27383step1Labels = raw27383step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1940 node1940Labels := by rfl

def raw27384 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw27384Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw27384step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27384step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw27384step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27384 raw27384Labels = mixedMoment B node1907 node1907Labels := by
  calc
    mixedMoment B raw27384 raw27384Labels = mixedMoment B raw27384step0 raw27384step0Labels := by
      have ha : raw27384step0 = (fun i j => raw27384 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27384step0 raw27384; decide +kernel
      have hl : raw27384step0Labels = raw27384Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27384 raw27384Labels permutation164 permutation4
    mixedMoment B raw27384step0 raw27384step0Labels = mixedMoment B raw27384step1 raw27384step1Labels := by
      have ha : raw27384step1 = -raw27384step0 := by apply Matrix.ext; change ∀ i j, raw27384step1 i j = -(raw27384step0 i j); unfold raw27384step1 raw27384step0; decide +kernel
      have hl : raw27384step1Labels = raw27384step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1907 node1907Labels := by rfl

def raw27385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27385Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27385step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27385 raw27385Labels = mixedMoment B node1793 node1793Labels := by
  calc
    mixedMoment B raw27385 raw27385Labels = mixedMoment B raw27385step0 raw27385step0Labels := by
      have ha : raw27385step0 = (fun i j => raw27385 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27385step0 raw27385; decide +kernel
      have hl : raw27385step0Labels = raw27385Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27385 raw27385Labels permutation158 permutation2
    _ = mixedMoment B node1793 node1793Labels := by rfl

def raw27386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27386Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw27386step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27386 raw27386Labels = mixedMoment B node1976 node1976Labels := by
  calc
    mixedMoment B raw27386 raw27386Labels = mixedMoment B raw27386step0 raw27386step0Labels := by
      have ha : raw27386step0 = (fun i j => raw27386 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27386step0 raw27386; decide +kernel
      have hl : raw27386step0Labels = raw27386Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27386 raw27386Labels permutation158 permutation2
    _ = mixedMoment B node1976 node1976Labels := by rfl

def raw27387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27387Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27387step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27387 raw27387Labels = mixedMoment B node2023 node2023Labels := by
  calc
    mixedMoment B raw27387 raw27387Labels = mixedMoment B raw27387step0 raw27387step0Labels := by
      have ha : raw27387step0 = (fun i j => raw27387 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27387step0 raw27387; decide +kernel
      have hl : raw27387step0Labels = raw27387Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27387 raw27387Labels permutation158 permutation2
    _ = mixedMoment B node2023 node2023Labels := by rfl

def raw27388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27388Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw27388step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27388step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw27388step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27388 raw27388Labels = mixedMoment B node1903 node1903Labels := by
  calc
    mixedMoment B raw27388 raw27388Labels = mixedMoment B raw27388step0 raw27388step0Labels := by
      have ha : raw27388step0 = (fun i j => raw27388 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27388step0 raw27388; decide +kernel
      have hl : raw27388step0Labels = raw27388Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27388 raw27388Labels permutation682 permutation2
    mixedMoment B raw27388step0 raw27388step0Labels = mixedMoment B raw27388step1 raw27388step1Labels := by
      have ha : raw27388step1 = -raw27388step0 := by apply Matrix.ext; change ∀ i j, raw27388step1 i j = -(raw27388step0 i j); unfold raw27388step1 raw27388step0; decide +kernel
      have hl : raw27388step1Labels = raw27388step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1903 node1903Labels := by rfl

def raw27389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27389Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw27389step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27389step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw27389step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27389 raw27389Labels = mixedMoment B node1904 node1904Labels := by
  calc
    mixedMoment B raw27389 raw27389Labels = mixedMoment B raw27389step0 raw27389step0Labels := by
      have ha : raw27389step0 = (fun i j => raw27389 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27389step0 raw27389; decide +kernel
      have hl : raw27389step0Labels = raw27389Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27389 raw27389Labels permutation681 permutation2
    mixedMoment B raw27389step0 raw27389step0Labels = mixedMoment B raw27389step1 raw27389step1Labels := by
      have ha : raw27389step1 = -raw27389step0 := by apply Matrix.ext; change ∀ i j, raw27389step1 i j = -(raw27389step0 i j); unfold raw27389step1 raw27389step0; decide +kernel
      have hl : raw27389step1Labels = raw27389step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1904 node1904Labels := by rfl

def raw27390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27390Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27390step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27390step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27390step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27390 raw27390Labels = mixedMoment B node1925 node1925Labels := by
  calc
    mixedMoment B raw27390 raw27390Labels = mixedMoment B raw27390step0 raw27390step0Labels := by
      have ha : raw27390step0 = (fun i j => raw27390 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27390step0 raw27390; decide +kernel
      have hl : raw27390step0Labels = raw27390Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27390 raw27390Labels permutation686 permutation2
    mixedMoment B raw27390step0 raw27390step0Labels = mixedMoment B raw27390step1 raw27390step1Labels := by
      have ha : raw27390step1 = -raw27390step0 := by apply Matrix.ext; change ∀ i j, raw27390step1 i j = -(raw27390step0 i j); unfold raw27390step1 raw27390step0; decide +kernel
      have hl : raw27390step1Labels = raw27390step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1925 node1925Labels := by rfl

def raw27391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw27391Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw27391step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27391step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27391step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27391 raw27391Labels = mixedMoment B node1913 node1913Labels := by
  calc
    mixedMoment B raw27391 raw27391Labels = mixedMoment B raw27391step0 raw27391step0Labels := by
      have ha : raw27391step0 = (fun i j => raw27391 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27391step0 raw27391; decide +kernel
      have hl : raw27391step0Labels = raw27391Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27391 raw27391Labels permutation680 permutation2
    mixedMoment B raw27391step0 raw27391step0Labels = mixedMoment B raw27391step1 raw27391step1Labels := by
      have ha : raw27391step1 = -raw27391step0 := by apply Matrix.ext; change ∀ i j, raw27391step1 i j = -(raw27391step0 i j); unfold raw27391step1 raw27391step0; decide +kernel
      have hl : raw27391step1Labels = raw27391step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1913 node1913Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
