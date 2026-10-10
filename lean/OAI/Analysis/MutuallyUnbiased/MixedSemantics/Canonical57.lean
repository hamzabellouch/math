import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw7296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw7296step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw7296step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7296 raw7296Labels = mixedMoment B node4580 node4580Labels := by
  calc
    mixedMoment B raw7296 raw7296Labels = mixedMoment B raw7296step0 raw7296step0Labels := by
      have ha : raw7296step0 = (fun i j => raw7296 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7296step0 raw7296; decide +kernel
      have hl : raw7296step0Labels = raw7296Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7296 raw7296Labels permutation184 permutation3
    mixedMoment B raw7296step0 raw7296step0Labels = mixedMoment B raw7296step1 raw7296step1Labels := by
      have ha : raw7296step1 = raw7296step0 := by apply Matrix.ext; unfold raw7296step1 raw7296step0; decide +kernel
      have hl : raw7296step0Labels = labelEmbedding6 ∘ raw7296step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7296step0 raw7296step0Labels raw7296step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4580 node4580Labels := by rfl

def raw7297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw7297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7297 raw7297Labels = mixedMoment B node5191 node5191Labels := by
  calc
    mixedMoment B raw7297 raw7297Labels = mixedMoment B raw7297step0 raw7297step0Labels := by
      have ha : raw7297step0 = (fun i j => raw7297 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7297step0 raw7297; decide +kernel
      have hl : raw7297step0Labels = raw7297Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7297 raw7297Labels permutation182 permutation2
    _ = mixedMoment B node5191 node5191Labels := by rfl

def raw7298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7298step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw7298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7298 raw7298Labels = mixedMoment B node5191 node5191Labels := by
  calc
    mixedMoment B raw7298 raw7298Labels = mixedMoment B raw7298step0 raw7298step0Labels := by
      have ha : raw7298step0 = (fun i j => raw7298 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7298step0 raw7298; decide +kernel
      have hl : raw7298step0Labels = raw7298Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7298 raw7298Labels permutation206 permutation2
    _ = mixedMoment B node5191 node5191Labels := by rfl

def raw7299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7299step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw7299step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7299 raw7299Labels = mixedMoment B node5277 node5277Labels := by
  calc
    mixedMoment B raw7299 raw7299Labels = mixedMoment B raw7299step0 raw7299step0Labels := by
      have ha : raw7299step0 = (fun i j => raw7299 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7299step0 raw7299; decide +kernel
      have hl : raw7299step0Labels = raw7299Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7299 raw7299Labels permutation184 permutation2
    _ = mixedMoment B node5277 node5277Labels := by rfl

def raw7300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw7300step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7300 raw7300Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw7300 raw7300Labels = mixedMoment B raw7300step0 raw7300step0Labels := by
      have ha : raw7300step0 = (fun i j => raw7300 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7300step0 raw7300; decide +kernel
      have hl : raw7300step0Labels = raw7300Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7300 raw7300Labels permutation183 permutation2
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw7301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7301step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7301step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7301step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7301step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7301 raw7301Labels = mixedMoment B node4589 node4589Labels := by
  calc
    mixedMoment B raw7301 raw7301Labels = mixedMoment B raw7301step0 raw7301step0Labels := by
      have ha : raw7301step0 = (fun i j => raw7301 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7301step0 raw7301; decide +kernel
      have hl : raw7301step0Labels = raw7301Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7301 raw7301Labels permutation200 permutation3
    mixedMoment B raw7301step0 raw7301step0Labels = mixedMoment B raw7301step1 raw7301step1Labels := by
      have ha : raw7301step1 = raw7301step0 := by apply Matrix.ext; unfold raw7301step1 raw7301step0; decide +kernel
      have hl : raw7301step0Labels = labelEmbedding6 ∘ raw7301step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7301step0 raw7301step0Labels raw7301step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4589 node4589Labels := by rfl

def raw7302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7302step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7302 raw7302Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw7302 raw7302Labels = mixedMoment B raw7302step0 raw7302step0Labels := by
      have ha : raw7302step0 = (fun i j => raw7302 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7302step0 raw7302; decide +kernel
      have hl : raw7302step0Labels = raw7302Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7302 raw7302Labels permutation158 permutation2
    _ = mixedMoment B node5076 node5076Labels := by rfl

def raw7303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7303step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7303 raw7303Labels = mixedMoment B node5187 node5187Labels := by
  calc
    mixedMoment B raw7303 raw7303Labels = mixedMoment B raw7303step0 raw7303step0Labels := by
      have ha : raw7303step0 = (fun i j => raw7303 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7303step0 raw7303; decide +kernel
      have hl : raw7303step0Labels = raw7303Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7303 raw7303Labels permutation200 permutation2
    _ = mixedMoment B node5187 node5187Labels := by rfl

def raw7304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7304step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7304step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7304 raw7304Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw7304 raw7304Labels = mixedMoment B raw7304step0 raw7304step0Labels := by
      have ha : raw7304step0 = (fun i j => raw7304 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7304step0 raw7304; decide +kernel
      have hl : raw7304step0Labels = raw7304Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7304 raw7304Labels permutation160 permutation2
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw7305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7305step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7305 raw7305Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw7305 raw7305Labels = mixedMoment B raw7305step0 raw7305step0Labels := by
      have ha : raw7305step0 = (fun i j => raw7305 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7305step0 raw7305; decide +kernel
      have hl : raw7305step0Labels = raw7305Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7305 raw7305Labels permutation162 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw7306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7306step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7306step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7306step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7306step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7306 raw7306Labels = mixedMoment B node4589 node4589Labels := by
  calc
    mixedMoment B raw7306 raw7306Labels = mixedMoment B raw7306step0 raw7306step0Labels := by
      have ha : raw7306step0 = (fun i j => raw7306 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7306step0 raw7306; decide +kernel
      have hl : raw7306step0Labels = raw7306Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7306 raw7306Labels permutation176 permutation3
    mixedMoment B raw7306step0 raw7306step0Labels = mixedMoment B raw7306step1 raw7306step1Labels := by
      have ha : raw7306step1 = raw7306step0 := by apply Matrix.ext; unfold raw7306step1 raw7306step0; decide +kernel
      have hl : raw7306step0Labels = labelEmbedding6 ∘ raw7306step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7306step0 raw7306step0Labels raw7306step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4589 node4589Labels := by rfl

def raw7307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7307 raw7307Labels = mixedMoment B node5076 node5076Labels := by
  calc
    _ = mixedMoment B node5076 node5076Labels := by rfl

def raw7308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7308step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7308 raw7308Labels = mixedMoment B node5187 node5187Labels := by
  calc
    mixedMoment B raw7308 raw7308Labels = mixedMoment B raw7308step0 raw7308step0Labels := by
      have ha : raw7308step0 = (fun i j => raw7308 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7308step0 raw7308; decide +kernel
      have hl : raw7308step0Labels = raw7308Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7308 raw7308Labels permutation176 permutation2
    _ = mixedMoment B node5187 node5187Labels := by rfl

def raw7309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7309step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7309step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7309 raw7309Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw7309 raw7309Labels = mixedMoment B raw7309step0 raw7309step0Labels := by
      have ha : raw7309step0 = (fun i j => raw7309 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7309step0 raw7309; decide +kernel
      have hl : raw7309step0Labels = raw7309Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7309 raw7309Labels permutation154 permutation2
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw7310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7310step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7310 raw7310Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw7310 raw7310Labels = mixedMoment B raw7310step0 raw7310step0Labels := by
      have ha : raw7310step0 = (fun i j => raw7310 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7310step0 raw7310; decide +kernel
      have hl : raw7310step0Labels = raw7310Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7310 raw7310Labels permutation156 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw7311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw7311step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7311step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw7311step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7311 raw7311Labels = mixedMoment B node4578 node4578Labels := by
  calc
    mixedMoment B raw7311 raw7311Labels = mixedMoment B raw7311step0 raw7311step0Labels := by
      have ha : raw7311step0 = (fun i j => raw7311 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7311step0 raw7311; decide +kernel
      have hl : raw7311step0Labels = raw7311Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7311 raw7311Labels permutation182 permutation3
    mixedMoment B raw7311step0 raw7311step0Labels = mixedMoment B raw7311step1 raw7311step1Labels := by
      have ha : raw7311step1 = raw7311step0 := by apply Matrix.ext; unfold raw7311step1 raw7311step0; decide +kernel
      have hl : raw7311step0Labels = labelEmbedding6 ∘ raw7311step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7311step0 raw7311step0Labels raw7311step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4578 node4578Labels := by rfl

def raw7312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7312step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7312 raw7312Labels = mixedMoment B node5067 node5067Labels := by
  calc
    mixedMoment B raw7312 raw7312Labels = mixedMoment B raw7312step0 raw7312step0Labels := by
      have ha : raw7312step0 = (fun i j => raw7312 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7312step0 raw7312; decide +kernel
      have hl : raw7312step0Labels = raw7312Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7312 raw7312Labels permutation153 permutation2
    _ = mixedMoment B node5067 node5067Labels := by rfl

def raw7313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7313step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7313step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7313 raw7313Labels = mixedMoment B node5182 node5182Labels := by
  calc
    mixedMoment B raw7313 raw7313Labels = mixedMoment B raw7313step0 raw7313step0Labels := by
      have ha : raw7313step0 = (fun i j => raw7313 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7313step0 raw7313; decide +kernel
      have hl : raw7313step0Labels = raw7313Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7313 raw7313Labels permutation177 permutation2
    _ = mixedMoment B node5182 node5182Labels := by rfl

def raw7314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7314step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7314 raw7314Labels = mixedMoment B node5182 node5182Labels := by
  calc
    mixedMoment B raw7314 raw7314Labels = mixedMoment B raw7314step0 raw7314step0Labels := by
      have ha : raw7314step0 = (fun i j => raw7314 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7314step0 raw7314; decide +kernel
      have hl : raw7314step0Labels = raw7314Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7314 raw7314Labels permutation201 permutation2
    _ = mixedMoment B node5182 node5182Labels := by rfl

def raw7315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw7315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw7315step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7315 raw7315Labels = mixedMoment B node5250 node5250Labels := by
  calc
    mixedMoment B raw7315 raw7315Labels = mixedMoment B raw7315step0 raw7315step0Labels := by
      have ha : raw7315step0 = (fun i j => raw7315 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7315step0 raw7315; decide +kernel
      have hl : raw7315step0Labels = raw7315Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7315 raw7315Labels permutation153 permutation2
    _ = mixedMoment B node5250 node5250Labels := by rfl

def raw7316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw7316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw7316step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw7316step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7316 raw7316Labels = mixedMoment B node4576 node4576Labels := by
  calc
    mixedMoment B raw7316 raw7316Labels = mixedMoment B raw7316step0 raw7316step0Labels := by
      have ha : raw7316step0 = (fun i j => raw7316 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7316step0 raw7316; decide +kernel
      have hl : raw7316step0Labels = raw7316Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7316 raw7316Labels permutation182 permutation3
    mixedMoment B raw7316step0 raw7316step0Labels = mixedMoment B raw7316step1 raw7316step1Labels := by
      have ha : raw7316step1 = raw7316step0 := by apply Matrix.ext; unfold raw7316step1 raw7316step0; decide +kernel
      have hl : raw7316step0Labels = labelEmbedding6 ∘ raw7316step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7316step0 raw7316step0Labels raw7316step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4576 node4576Labels := by rfl

def raw7317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw7317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw7317step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7317step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7317step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7317step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7317step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7317 raw7317Labels = mixedMoment B node4792 node4792Labels := by
  calc
    mixedMoment B raw7317 raw7317Labels = mixedMoment B raw7317step0 raw7317step0Labels := by
      have ha : raw7317step0 = (fun i j => raw7317 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7317step0 raw7317; decide +kernel
      have hl : raw7317step0Labels = raw7317Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7317 raw7317Labels permutation682 permutation3
    mixedMoment B raw7317step0 raw7317step0Labels = mixedMoment B raw7317step1 raw7317step1Labels := by
      have ha : raw7317step1 = -raw7317step0 := by apply Matrix.ext; change ∀ i j, raw7317step1 i j = -(raw7317step0 i j); unfold raw7317step1 raw7317step0; decide +kernel
      have hl : raw7317step1Labels = raw7317step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7317step1 raw7317step1Labels = mixedMoment B raw7317step2 raw7317step2Labels := by
      have ha : raw7317step2 = raw7317step1 := by apply Matrix.ext; unfold raw7317step2 raw7317step1; decide +kernel
      have hl : raw7317step1Labels = labelEmbedding6 ∘ raw7317step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7317step1 raw7317step1Labels raw7317step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4792 node4792Labels := by rfl

def raw7318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw7318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw7318step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7318step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw7318step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7318step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw7318step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7318 raw7318Labels = mixedMoment B node4780 node4780Labels := by
  calc
    mixedMoment B raw7318 raw7318Labels = mixedMoment B raw7318step0 raw7318step0Labels := by
      have ha : raw7318step0 = (fun i j => raw7318 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7318step0 raw7318; decide +kernel
      have hl : raw7318step0Labels = raw7318Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7318 raw7318Labels permutation676 permutation3
    mixedMoment B raw7318step0 raw7318step0Labels = mixedMoment B raw7318step1 raw7318step1Labels := by
      have ha : raw7318step1 = -raw7318step0 := by apply Matrix.ext; change ∀ i j, raw7318step1 i j = -(raw7318step0 i j); unfold raw7318step1 raw7318step0; decide +kernel
      have hl : raw7318step1Labels = raw7318step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7318step1 raw7318step1Labels = mixedMoment B raw7318step2 raw7318step2Labels := by
      have ha : raw7318step2 = raw7318step1 := by apply Matrix.ext; unfold raw7318step2 raw7318step1; decide +kernel
      have hl : raw7318step1Labels = labelEmbedding6 ∘ raw7318step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7318step1 raw7318step1Labels raw7318step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4780 node4780Labels := by rfl

def raw7319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw7319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw7319step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7319step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw7319step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7319step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw7319step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7319 raw7319Labels = mixedMoment B node4780 node4780Labels := by
  calc
    mixedMoment B raw7319 raw7319Labels = mixedMoment B raw7319step0 raw7319step0Labels := by
      have ha : raw7319step0 = (fun i j => raw7319 (permutation674 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7319step0 raw7319; decide +kernel
      have hl : raw7319step0Labels = raw7319Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7319 raw7319Labels permutation674 permutation3
    mixedMoment B raw7319step0 raw7319step0Labels = mixedMoment B raw7319step1 raw7319step1Labels := by
      have ha : raw7319step1 = -raw7319step0 := by apply Matrix.ext; change ∀ i j, raw7319step1 i j = -(raw7319step0 i j); unfold raw7319step1 raw7319step0; decide +kernel
      have hl : raw7319step1Labels = raw7319step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7319step1 raw7319step1Labels = mixedMoment B raw7319step2 raw7319step2Labels := by
      have ha : raw7319step2 = raw7319step1 := by apply Matrix.ext; unfold raw7319step2 raw7319step1; decide +kernel
      have hl : raw7319step1Labels = labelEmbedding6 ∘ raw7319step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7319step1 raw7319step1Labels raw7319step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4780 node4780Labels := by rfl

def raw7320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw7320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7320step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw7320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7320step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7320 raw7320Labels = mixedMoment B node4830 node4830Labels := by
  calc
    mixedMoment B raw7320 raw7320Labels = mixedMoment B raw7320step0 raw7320step0Labels := by
      have ha : raw7320step0 = (fun i j => raw7320 (permutation609 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7320step0 raw7320; decide +kernel
      have hl : raw7320step0Labels = raw7320Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7320 raw7320Labels permutation609 permutation5
    mixedMoment B raw7320step0 raw7320step0Labels = mixedMoment B raw7320step1 raw7320step1Labels := by
      have ha : raw7320step1 = raw7320step0 := by apply Matrix.ext; unfold raw7320step1 raw7320step0; decide +kernel
      have hl : raw7320step0Labels = labelEmbedding8 ∘ raw7320step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7320step0 raw7320step0Labels raw7320step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4830 node4830Labels := by rfl

def raw7321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7321Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw7321step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7321step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw7321step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7321 raw7321Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw7321 raw7321Labels = mixedMoment B raw7321step0 raw7321step0Labels := by
      have ha : raw7321step0 = (fun i j => raw7321 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7321step0 raw7321; decide +kernel
      have hl : raw7321step0Labels = raw7321Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7321 raw7321Labels permutation682 permutation3
    mixedMoment B raw7321step0 raw7321step0Labels = mixedMoment B raw7321step1 raw7321step1Labels := by
      have ha : raw7321step1 = -raw7321step0 := by apply Matrix.ext; change ∀ i j, raw7321step1 i j = -(raw7321step0 i j); unfold raw7321step1 raw7321step0; decide +kernel
      have hl : raw7321step1Labels = raw7321step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3847 node3847Labels := by rfl

def raw7322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7322Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw7322step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7322step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7322 raw7322Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw7322 raw7322Labels = mixedMoment B raw7322step0 raw7322step0Labels := by
      have ha : raw7322step0 = (fun i j => raw7322 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7322step0 raw7322; decide +kernel
      have hl : raw7322step0Labels = raw7322Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7322 raw7322Labels permutation676 permutation3
    mixedMoment B raw7322step0 raw7322step0Labels = mixedMoment B raw7322step1 raw7322step1Labels := by
      have ha : raw7322step1 = -raw7322step0 := by apply Matrix.ext; change ∀ i j, raw7322step1 i j = -(raw7322step0 i j); unfold raw7322step1 raw7322step0; decide +kernel
      have hl : raw7322step1Labels = raw7322step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw7323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7323Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw7323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7323step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7323 raw7323Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw7323 raw7323Labels = mixedMoment B raw7323step0 raw7323step0Labels := by
      have ha : raw7323step0 = (fun i j => raw7323 (permutation674 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7323step0 raw7323; decide +kernel
      have hl : raw7323step0Labels = raw7323Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7323 raw7323Labels permutation674 permutation3
    mixedMoment B raw7323step0 raw7323step0Labels = mixedMoment B raw7323step1 raw7323step1Labels := by
      have ha : raw7323step1 = -raw7323step0 := by apply Matrix.ext; change ∀ i j, raw7323step1 i j = -(raw7323step0 i j); unfold raw7323step1 raw7323step0; decide +kernel
      have hl : raw7323step1Labels = raw7323step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw7324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7324Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7324step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw7324step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7324step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7324step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7324 raw7324Labels = mixedMoment B node3899 node3899Labels := by
  calc
    mixedMoment B raw7324 raw7324Labels = mixedMoment B raw7324step0 raw7324step0Labels := by
      have ha : raw7324step0 = (fun i j => raw7324 (permutation609 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7324step0 raw7324; decide +kernel
      have hl : raw7324step0Labels = raw7324Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7324 raw7324Labels permutation609 permutation3
    mixedMoment B raw7324step0 raw7324step0Labels = mixedMoment B raw7324step1 raw7324step1Labels := by
      have ha : raw7324step1 = -raw7324step0 := by apply Matrix.ext; change ∀ i j, raw7324step1 i j = -(raw7324step0 i j); unfold raw7324step1 raw7324step0; decide +kernel
      have hl : raw7324step1Labels = raw7324step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3899 node3899Labels := by rfl

def raw7325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7325Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw7325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7325step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7325step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7325 raw7325Labels = mixedMoment B node4033 node4033Labels := by
  calc
    mixedMoment B raw7325 raw7325Labels = mixedMoment B raw7325step0 raw7325step0Labels := by
      have ha : raw7325step0 = (fun i j => raw7325 (permutation174 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7325step0 raw7325; decide +kernel
      have hl : raw7325step0Labels = raw7325Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7325 raw7325Labels permutation174 permutation6
    mixedMoment B raw7325step0 raw7325step0Labels = mixedMoment B raw7325step1 raw7325step1Labels := by
      have ha : raw7325step1 = -raw7325step0 := by apply Matrix.ext; change ∀ i j, raw7325step1 i j = -(raw7325step0 i j); unfold raw7325step1 raw7325step0; decide +kernel
      have hl : raw7325step1Labels = raw7325step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4033 node4033Labels := by rfl

def raw7326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7326Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7326step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw7326step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7326 raw7326Labels = mixedMoment B node1198 node1198Labels := by
  calc
    mixedMoment B raw7326 raw7326Labels = mixedMoment B raw7326step0 raw7326step0Labels := by
      have ha : raw7326step0 = (fun i j => raw7326 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7326step0 raw7326; decide +kernel
      have hl : raw7326step0Labels = raw7326Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7326 raw7326Labels permutation184 permutation3
    _ = mixedMoment B node1198 node1198Labels := by rfl

def raw7327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7327Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7327step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw7327step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7327 raw7327Labels = mixedMoment B node2852 node2852Labels := by
  calc
    mixedMoment B raw7327 raw7327Labels = mixedMoment B raw7327step0 raw7327step0Labels := by
      have ha : raw7327step0 = (fun i j => raw7327 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7327step0 raw7327; decide +kernel
      have hl : raw7327step0Labels = raw7327Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7327 raw7327Labels permutation184 permutation3
    _ = mixedMoment B node2852 node2852Labels := by rfl

def raw7328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7328Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw7328step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7328 raw7328Labels = mixedMoment B node2852 node2852Labels := by
  calc
    mixedMoment B raw7328 raw7328Labels = mixedMoment B raw7328step0 raw7328step0Labels := by
      have ha : raw7328step0 = (fun i j => raw7328 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7328step0 raw7328; decide +kernel
      have hl : raw7328step0Labels = raw7328Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7328 raw7328Labels permutation208 permutation3
    _ = mixedMoment B node2852 node2852Labels := by rfl

def raw7329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7329Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7329step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw7329step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7329 raw7329Labels = mixedMoment B node3059 node3059Labels := by
  calc
    mixedMoment B raw7329 raw7329Labels = mixedMoment B raw7329step0 raw7329step0Labels := by
      have ha : raw7329step0 = (fun i j => raw7329 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7329step0 raw7329; decide +kernel
      have hl : raw7329step0Labels = raw7329Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7329 raw7329Labels permutation184 permutation3
    _ = mixedMoment B node3059 node3059Labels := by rfl

def raw7330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7330Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7330step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw7330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7330 raw7330Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw7330 raw7330Labels = mixedMoment B raw7330step0 raw7330step0Labels := by
      have ha : raw7330step0 = (fun i j => raw7330 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7330step0 raw7330; decide +kernel
      have hl : raw7330step0Labels = raw7330Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7330 raw7330Labels permutation185 permutation3
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw7331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7331Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7331 raw7331Labels = mixedMoment B node1212 node1212Labels := by
  calc
    mixedMoment B raw7331 raw7331Labels = mixedMoment B raw7331step0 raw7331step0Labels := by
      have ha : raw7331step0 = (fun i j => raw7331 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7331step0 raw7331; decide +kernel
      have hl : raw7331step0Labels = raw7331Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7331 raw7331Labels permutation200 permutation3
    _ = mixedMoment B node1212 node1212Labels := by rfl

def raw7332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7332Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7332step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7332 raw7332Labels = mixedMoment B node2986 node2986Labels := by
  calc
    mixedMoment B raw7332 raw7332Labels = mixedMoment B raw7332step0 raw7332step0Labels := by
      have ha : raw7332step0 = (fun i j => raw7332 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7332step0 raw7332; decide +kernel
      have hl : raw7332step0Labels = raw7332Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7332 raw7332Labels permutation158 permutation3
    _ = mixedMoment B node2986 node2986Labels := by rfl

def raw7333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7333Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7333step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7333step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7333 raw7333Labels = mixedMoment B node2861 node2861Labels := by
  calc
    mixedMoment B raw7333 raw7333Labels = mixedMoment B raw7333step0 raw7333step0Labels := by
      have ha : raw7333step0 = (fun i j => raw7333 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7333step0 raw7333; decide +kernel
      have hl : raw7333step0Labels = raw7333Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7333 raw7333Labels permutation200 permutation3
    _ = mixedMoment B node2861 node2861Labels := by rfl

def raw7334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7334Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7334 raw7334Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw7334 raw7334Labels = mixedMoment B raw7334step0 raw7334step0Labels := by
      have ha : raw7334step0 = (fun i j => raw7334 (permutation212 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7334step0 raw7334; decide +kernel
      have hl : raw7334step0Labels = raw7334Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7334 raw7334Labels permutation212 permutation3
    _ = mixedMoment B node3064 node3064Labels := by rfl

def raw7335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7335Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7335 raw7335Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw7335 raw7335Labels = mixedMoment B raw7335step0 raw7335step0Labels := by
      have ha : raw7335step0 = (fun i j => raw7335 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7335step0 raw7335; decide +kernel
      have hl : raw7335step0Labels = raw7335Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7335 raw7335Labels permutation200 permutation3
    _ = mixedMoment B node3087 node3087Labels := by rfl

def raw7336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7336Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7336 raw7336Labels = mixedMoment B node1212 node1212Labels := by
  calc
    mixedMoment B raw7336 raw7336Labels = mixedMoment B raw7336step0 raw7336step0Labels := by
      have ha : raw7336step0 = (fun i j => raw7336 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7336step0 raw7336; decide +kernel
      have hl : raw7336step0Labels = raw7336Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7336 raw7336Labels permutation176 permutation3
    _ = mixedMoment B node1212 node1212Labels := by rfl

def raw7337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7337Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7337 raw7337Labels = mixedMoment B node2986 node2986Labels := by
  calc
    mixedMoment B raw7337 raw7337Labels = mixedMoment B raw7337step0 raw7337step0Labels := by
      have ha : raw7337step0 = (fun i j => raw7337 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7337step0 raw7337; decide +kernel
      have hl : raw7337step0Labels = raw7337Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7337 raw7337Labels permutation152 permutation3
    _ = mixedMoment B node2986 node2986Labels := by rfl

def raw7338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7338Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw7338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7338 raw7338Labels = mixedMoment B node2861 node2861Labels := by
  calc
    mixedMoment B raw7338 raw7338Labels = mixedMoment B raw7338step0 raw7338step0Labels := by
      have ha : raw7338step0 = (fun i j => raw7338 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7338step0 raw7338; decide +kernel
      have hl : raw7338step0Labels = raw7338Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7338 raw7338Labels permutation176 permutation3
    _ = mixedMoment B node2861 node2861Labels := by rfl

def raw7339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7339Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7339 raw7339Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw7339 raw7339Labels = mixedMoment B raw7339step0 raw7339step0Labels := by
      have ha : raw7339step0 = (fun i j => raw7339 (permutation188 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7339step0 raw7339; decide +kernel
      have hl : raw7339step0Labels = raw7339Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7339 raw7339Labels permutation188 permutation3
    _ = mixedMoment B node3064 node3064Labels := by rfl

def raw7340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7340Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7340 raw7340Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw7340 raw7340Labels = mixedMoment B raw7340step0 raw7340step0Labels := by
      have ha : raw7340step0 = (fun i j => raw7340 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7340step0 raw7340; decide +kernel
      have hl : raw7340step0Labels = raw7340Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7340 raw7340Labels permutation176 permutation3
    _ = mixedMoment B node3087 node3087Labels := by rfl

def raw7341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7341Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw7341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7341 raw7341Labels = mixedMoment B node1196 node1196Labels := by
  calc
    mixedMoment B raw7341 raw7341Labels = mixedMoment B raw7341step0 raw7341step0Labels := by
      have ha : raw7341step0 = (fun i j => raw7341 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7341step0 raw7341; decide +kernel
      have hl : raw7341step0Labels = raw7341Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7341 raw7341Labels permutation182 permutation3
    _ = mixedMoment B node1196 node1196Labels := by rfl

def raw7342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7342Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7342step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw7342step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7342 raw7342Labels = mixedMoment B node2981 node2981Labels := by
  calc
    mixedMoment B raw7342 raw7342Labels = mixedMoment B raw7342step0 raw7342step0Labels := by
      have ha : raw7342step0 = (fun i j => raw7342 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7342step0 raw7342; decide +kernel
      have hl : raw7342step0Labels = raw7342Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7342 raw7342Labels permutation152 permutation3
    _ = mixedMoment B node2981 node2981Labels := by rfl

def raw7343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7343Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw7343step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7343 raw7343Labels = mixedMoment B node2850 node2850Labels := by
  calc
    mixedMoment B raw7343 raw7343Labels = mixedMoment B raw7343step0 raw7343step0Labels := by
      have ha : raw7343step0 = (fun i j => raw7343 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7343step0 raw7343; decide +kernel
      have hl : raw7343step0Labels = raw7343Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7343 raw7343Labels permutation182 permutation3
    _ = mixedMoment B node2850 node2850Labels := by rfl

def raw7344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7344Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7344step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw7344step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7344 raw7344Labels = mixedMoment B node2850 node2850Labels := by
  calc
    mixedMoment B raw7344 raw7344Labels = mixedMoment B raw7344step0 raw7344step0Labels := by
      have ha : raw7344step0 = (fun i j => raw7344 (permutation206 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7344step0 raw7344; decide +kernel
      have hl : raw7344step0Labels = raw7344Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7344 raw7344Labels permutation206 permutation3
    _ = mixedMoment B node2850 node2850Labels := by rfl

def raw7345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw7345Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7345step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7345 raw7345Labels = mixedMoment B node3065 node3065Labels := by
  calc
    mixedMoment B raw7345 raw7345Labels = mixedMoment B raw7345step0 raw7345step0Labels := by
      have ha : raw7345step0 = (fun i j => raw7345 (permutation183 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7345step0 raw7345; decide +kernel
      have hl : raw7345step0Labels = raw7345Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7345 raw7345Labels permutation183 permutation3
    _ = mixedMoment B node3065 node3065Labels := by rfl

def raw7346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw7346Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw7346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7346 raw7346Labels = mixedMoment B node1194 node1194Labels := by
  calc
    mixedMoment B raw7346 raw7346Labels = mixedMoment B raw7346step0 raw7346step0Labels := by
      have ha : raw7346step0 = (fun i j => raw7346 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7346step0 raw7346; decide +kernel
      have hl : raw7346step0Labels = raw7346Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7346 raw7346Labels permutation182 permutation3
    _ = mixedMoment B node1194 node1194Labels := by rfl

def raw7347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw7347Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw7347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7347step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw7347step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7347 raw7347Labels = mixedMoment B node2009 node2009Labels := by
  calc
    mixedMoment B raw7347 raw7347Labels = mixedMoment B raw7347step0 raw7347step0Labels := by
      have ha : raw7347step0 = (fun i j => raw7347 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7347step0 raw7347; decide +kernel
      have hl : raw7347step0Labels = raw7347Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7347 raw7347Labels permutation682 permutation3
    mixedMoment B raw7347step0 raw7347step0Labels = mixedMoment B raw7347step1 raw7347step1Labels := by
      have ha : raw7347step1 = -raw7347step0 := by apply Matrix.ext; change ∀ i j, raw7347step1 i j = -(raw7347step0 i j); unfold raw7347step1 raw7347step0; decide +kernel
      have hl : raw7347step1Labels = raw7347step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2009 node2009Labels := by rfl

def raw7348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw7348Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw7348step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7348step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw7348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7348 raw7348Labels = mixedMoment B node1988 node1988Labels := by
  calc
    mixedMoment B raw7348 raw7348Labels = mixedMoment B raw7348step0 raw7348step0Labels := by
      have ha : raw7348step0 = (fun i j => raw7348 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7348step0 raw7348; decide +kernel
      have hl : raw7348step0Labels = raw7348Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7348 raw7348Labels permutation676 permutation3
    mixedMoment B raw7348step0 raw7348step0Labels = mixedMoment B raw7348step1 raw7348step1Labels := by
      have ha : raw7348step1 = -raw7348step0 := by apply Matrix.ext; change ∀ i j, raw7348step1 i j = -(raw7348step0 i j); unfold raw7348step1 raw7348step0; decide +kernel
      have hl : raw7348step1Labels = raw7348step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1988 node1988Labels := by rfl

def raw7349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw7349Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7349step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw7349step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7349step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw7349step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7349 raw7349Labels = mixedMoment B node1988 node1988Labels := by
  calc
    mixedMoment B raw7349 raw7349Labels = mixedMoment B raw7349step0 raw7349step0Labels := by
      have ha : raw7349step0 = (fun i j => raw7349 (permutation674 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7349step0 raw7349; decide +kernel
      have hl : raw7349step0Labels = raw7349Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7349 raw7349Labels permutation674 permutation3
    mixedMoment B raw7349step0 raw7349step0Labels = mixedMoment B raw7349step1 raw7349step1Labels := by
      have ha : raw7349step1 = -raw7349step0 := by apply Matrix.ext; change ∀ i j, raw7349step1 i j = -(raw7349step0 i j); unfold raw7349step1 raw7349step0; decide +kernel
      have hl : raw7349step1Labels = raw7349step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1988 node1988Labels := by rfl

def raw7350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw7350Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw7350step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw7350step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7350step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw7350step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7350 raw7350Labels = mixedMoment B node2187 node2187Labels := by
  calc
    mixedMoment B raw7350 raw7350Labels = mixedMoment B raw7350step0 raw7350step0Labels := by
      have ha : raw7350step0 = (fun i j => raw7350 (permutation609 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7350step0 raw7350; decide +kernel
      have hl : raw7350step0Labels = raw7350Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7350 raw7350Labels permutation609 permutation3
    mixedMoment B raw7350step0 raw7350step0Labels = mixedMoment B raw7350step1 raw7350step1Labels := by
      have ha : raw7350step1 = -raw7350step0 := by apply Matrix.ext; change ∀ i j, raw7350step1 i j = -(raw7350step0 i j); unfold raw7350step1 raw7350step0; decide +kernel
      have hl : raw7350step1Labels = raw7350step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2187 node2187Labels := by rfl

def raw7351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7351Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw7351step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7351step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7351step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7351step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7351step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7351 raw7351Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw7351 raw7351Labels = mixedMoment B raw7351step0 raw7351step0Labels := by
      have ha : raw7351step0 = (fun i j => raw7351 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7351step0 raw7351; decide +kernel
      have hl : raw7351step0Labels = raw7351Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7351 raw7351Labels permutation170 permutation7
    mixedMoment B raw7351step0 raw7351step0Labels = mixedMoment B raw7351step1 raw7351step1Labels := by
      have ha : raw7351step1 = -raw7351step0 := by apply Matrix.ext; change ∀ i j, raw7351step1 i j = -(raw7351step0 i j); unfold raw7351step1 raw7351step0; decide +kernel
      have hl : raw7351step1Labels = raw7351step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7351step1 raw7351step1Labels = mixedMoment B raw7351step2 raw7351step2Labels := by
      have ha : raw7351step2 = raw7351step1 := by apply Matrix.ext; unfold raw7351step2 raw7351step1; decide +kernel
      have hl : raw7351step1Labels = labelEmbedding1 ∘ raw7351step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7351step1 raw7351step1Labels raw7351step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3812 node3812Labels := by rfl

def raw7352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7352Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7352step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7352step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7352step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7352 raw7352Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw7352 raw7352Labels = mixedMoment B raw7352step0 raw7352step0Labels := by
      have ha : raw7352step0 = (fun i j => raw7352 (permutation618 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7352step0 raw7352; decide +kernel
      have hl : raw7352step0Labels = raw7352Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7352 raw7352Labels permutation618 permutation5
    mixedMoment B raw7352step0 raw7352step0Labels = mixedMoment B raw7352step1 raw7352step1Labels := by
      have ha : raw7352step1 = raw7352step0 := by apply Matrix.ext; unfold raw7352step1 raw7352step0; decide +kernel
      have hl : raw7352step0Labels = labelEmbedding1 ∘ raw7352step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7352step0 raw7352step0Labels raw7352step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw7353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7353Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7353step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7353step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw7353step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7353 raw7353Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw7353 raw7353Labels = mixedMoment B raw7353step0 raw7353step0Labels := by
      have ha : raw7353step0 = (fun i j => raw7353 (permutation617 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7353step0 raw7353; decide +kernel
      have hl : raw7353step0Labels = raw7353Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7353 raw7353Labels permutation617 permutation5
    mixedMoment B raw7353step0 raw7353step0Labels = mixedMoment B raw7353step1 raw7353step1Labels := by
      have ha : raw7353step1 = raw7353step0 := by apply Matrix.ext; unfold raw7353step1 raw7353step0; decide +kernel
      have hl : raw7353step0Labels = labelEmbedding1 ∘ raw7353step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7353step0 raw7353step0Labels raw7353step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw7354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7354Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw7354step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7354step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw7354step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7354 raw7354Labels = mixedMoment B node3855 node3855Labels := by
  calc
    mixedMoment B raw7354 raw7354Labels = mixedMoment B raw7354step0 raw7354step0Labels := by
      have ha : raw7354step0 = (fun i j => raw7354 (permutation602 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7354step0 raw7354; decide +kernel
      have hl : raw7354step0Labels = raw7354Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7354 raw7354Labels permutation602 permutation5
    mixedMoment B raw7354step0 raw7354step0Labels = mixedMoment B raw7354step1 raw7354step1Labels := by
      have ha : raw7354step1 = raw7354step0 := by apply Matrix.ext; unfold raw7354step1 raw7354step0; decide +kernel
      have hl : raw7354step0Labels = labelEmbedding1 ∘ raw7354step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7354step0 raw7354step0Labels raw7354step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3855 node3855Labels := by rfl

def raw7355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7355Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7355step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw7355step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7355step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7355step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7355step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7355step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7355 raw7355Labels = mixedMoment B node3851 node3851Labels := by
  calc
    mixedMoment B raw7355 raw7355Labels = mixedMoment B raw7355step0 raw7355step0Labels := by
      have ha : raw7355step0 = (fun i j => raw7355 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7355step0 raw7355; decide +kernel
      have hl : raw7355step0Labels = raw7355Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7355 raw7355Labels permutation170 permutation7
    mixedMoment B raw7355step0 raw7355step0Labels = mixedMoment B raw7355step1 raw7355step1Labels := by
      have ha : raw7355step1 = -raw7355step0 := by apply Matrix.ext; change ∀ i j, raw7355step1 i j = -(raw7355step0 i j); unfold raw7355step1 raw7355step0; decide +kernel
      have hl : raw7355step1Labels = raw7355step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7355step1 raw7355step1Labels = mixedMoment B raw7355step2 raw7355step2Labels := by
      have ha : raw7355step2 = raw7355step1 := by apply Matrix.ext; unfold raw7355step2 raw7355step1; decide +kernel
      have hl : raw7355step1Labels = labelEmbedding1 ∘ raw7355step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7355step1 raw7355step1Labels raw7355step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3851 node3851Labels := by rfl

def raw7356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7356Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw7356step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7356step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw7356step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7356step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw7356step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7356 raw7356Labels = mixedMoment B node3278 node3278Labels := by
  calc
    mixedMoment B raw7356 raw7356Labels = mixedMoment B raw7356step0 raw7356step0Labels := by
      have ha : raw7356step0 = (fun i j => raw7356 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7356step0 raw7356; decide +kernel
      have hl : raw7356step0Labels = raw7356Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7356 raw7356Labels permutation184 permutation5
    mixedMoment B raw7356step0 raw7356step0Labels = mixedMoment B raw7356step1 raw7356step1Labels := by
      have ha : raw7356step1 = -raw7356step0 := by apply Matrix.ext; change ∀ i j, raw7356step1 i j = -(raw7356step0 i j); unfold raw7356step1 raw7356step0; decide +kernel
      have hl : raw7356step1Labels = raw7356step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7356step1 raw7356step1Labels = mixedMoment B raw7356step2 raw7356step2Labels := by
      have ha : raw7356step2 = raw7356step1 := by apply Matrix.ext; unfold raw7356step2 raw7356step1; decide +kernel
      have hl : raw7356step1Labels = labelEmbedding1 ∘ raw7356step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7356step1 raw7356step1Labels raw7356step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3278 node3278Labels := by rfl

def raw7357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7357Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw7357step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7357step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw7357step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7357step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw7357step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7357 raw7357Labels = mixedMoment B node3574 node3574Labels := by
  calc
    mixedMoment B raw7357 raw7357Labels = mixedMoment B raw7357step0 raw7357step0Labels := by
      have ha : raw7357step0 = (fun i j => raw7357 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7357step0 raw7357; decide +kernel
      have hl : raw7357step0Labels = raw7357Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7357 raw7357Labels permutation170 permutation7
    mixedMoment B raw7357step0 raw7357step0Labels = mixedMoment B raw7357step1 raw7357step1Labels := by
      have ha : raw7357step1 = -raw7357step0 := by apply Matrix.ext; change ∀ i j, raw7357step1 i j = -(raw7357step0 i j); unfold raw7357step1 raw7357step0; decide +kernel
      have hl : raw7357step1Labels = raw7357step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7357step1 raw7357step1Labels = mixedMoment B raw7357step2 raw7357step2Labels := by
      have ha : raw7357step2 = raw7357step1 := by apply Matrix.ext; unfold raw7357step2 raw7357step1; decide +kernel
      have hl : raw7357step1Labels = labelEmbedding1 ∘ raw7357step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7357step1 raw7357step1Labels raw7357step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3574 node3574Labels := by rfl

def raw7358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7358Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7358step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw7358step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7358step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw7358step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7358step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw7358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7358 raw7358Labels = mixedMoment B node3574 node3574Labels := by
  calc
    mixedMoment B raw7358 raw7358Labels = mixedMoment B raw7358step0 raw7358step0Labels := by
      have ha : raw7358step0 = (fun i j => raw7358 (permutation172 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7358step0 raw7358; decide +kernel
      have hl : raw7358step0Labels = raw7358Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7358 raw7358Labels permutation172 permutation7
    mixedMoment B raw7358step0 raw7358step0Labels = mixedMoment B raw7358step1 raw7358step1Labels := by
      have ha : raw7358step1 = -raw7358step0 := by apply Matrix.ext; change ∀ i j, raw7358step1 i j = -(raw7358step0 i j); unfold raw7358step1 raw7358step0; decide +kernel
      have hl : raw7358step1Labels = raw7358step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7358step1 raw7358step1Labels = mixedMoment B raw7358step2 raw7358step2Labels := by
      have ha : raw7358step2 = raw7358step1 := by apply Matrix.ext; unfold raw7358step2 raw7358step1; decide +kernel
      have hl : raw7358step1Labels = labelEmbedding1 ∘ raw7358step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7358step1 raw7358step1Labels raw7358step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3574 node3574Labels := by rfl

def raw7359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7359Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw7359step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7359step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw7359step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7359step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw7359step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7359 raw7359Labels = mixedMoment B node3576 node3576Labels := by
  calc
    mixedMoment B raw7359 raw7359Labels = mixedMoment B raw7359step0 raw7359step0Labels := by
      have ha : raw7359step0 = (fun i j => raw7359 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7359step0 raw7359; decide +kernel
      have hl : raw7359step0Labels = raw7359Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7359 raw7359Labels permutation170 permutation7
    mixedMoment B raw7359step0 raw7359step0Labels = mixedMoment B raw7359step1 raw7359step1Labels := by
      have ha : raw7359step1 = -raw7359step0 := by apply Matrix.ext; change ∀ i j, raw7359step1 i j = -(raw7359step0 i j); unfold raw7359step1 raw7359step0; decide +kernel
      have hl : raw7359step1Labels = raw7359step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7359step1 raw7359step1Labels = mixedMoment B raw7359step2 raw7359step2Labels := by
      have ha : raw7359step2 = raw7359step1 := by apply Matrix.ext; unfold raw7359step2 raw7359step1; decide +kernel
      have hl : raw7359step1Labels = labelEmbedding1 ∘ raw7359step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7359step1 raw7359step1Labels raw7359step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3576 node3576Labels := by rfl

def raw7360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7360Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw7360step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7360step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7360step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7360step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7360step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7360 raw7360Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw7360 raw7360Labels = mixedMoment B raw7360step0 raw7360step0Labels := by
      have ha : raw7360step0 = (fun i j => raw7360 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7360step0 raw7360; decide +kernel
      have hl : raw7360step0Labels = raw7360Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7360 raw7360Labels permutation170 permutation7
    mixedMoment B raw7360step0 raw7360step0Labels = mixedMoment B raw7360step1 raw7360step1Labels := by
      have ha : raw7360step1 = -raw7360step0 := by apply Matrix.ext; change ∀ i j, raw7360step1 i j = -(raw7360step0 i j); unfold raw7360step1 raw7360step0; decide +kernel
      have hl : raw7360step1Labels = raw7360step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7360step1 raw7360step1Labels = mixedMoment B raw7360step2 raw7360step2Labels := by
      have ha : raw7360step2 = raw7360step1 := by apply Matrix.ext; unfold raw7360step2 raw7360step1; decide +kernel
      have hl : raw7360step1Labels = labelEmbedding1 ∘ raw7360step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7360step1 raw7360step1Labels raw7360step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3571 node3571Labels := by rfl

def raw7361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7361Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw7361step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7361step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7361step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7361step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7361step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7361 raw7361Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw7361 raw7361Labels = mixedMoment B raw7361step0 raw7361step0Labels := by
      have ha : raw7361step0 = (fun i j => raw7361 (permutation208 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7361step0 raw7361; decide +kernel
      have hl : raw7361step0Labels = raw7361Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7361 raw7361Labels permutation208 permutation5
    mixedMoment B raw7361step0 raw7361step0Labels = mixedMoment B raw7361step1 raw7361step1Labels := by
      have ha : raw7361step1 = -raw7361step0 := by apply Matrix.ext; change ∀ i j, raw7361step1 i j = -(raw7361step0 i j); unfold raw7361step1 raw7361step0; decide +kernel
      have hl : raw7361step1Labels = raw7361step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7361step1 raw7361step1Labels = mixedMoment B raw7361step2 raw7361step2Labels := by
      have ha : raw7361step2 = raw7361step1 := by apply Matrix.ext; unfold raw7361step2 raw7361step1; decide +kernel
      have hl : raw7361step1Labels = labelEmbedding1 ∘ raw7361step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7361step1 raw7361step1Labels raw7361step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3288 node3288Labels := by rfl

def raw7362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7362Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw7362step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7362step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7362step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7362step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7362 raw7362Labels = mixedMoment B node3477 node3477Labels := by
  calc
    mixedMoment B raw7362 raw7362Labels = mixedMoment B raw7362step0 raw7362step0Labels := by
      have ha : raw7362step0 = (fun i j => raw7362 (permutation172 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7362step0 raw7362; decide +kernel
      have hl : raw7362step0Labels = raw7362Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7362 raw7362Labels permutation172 permutation7
    mixedMoment B raw7362step0 raw7362step0Labels = mixedMoment B raw7362step1 raw7362step1Labels := by
      have ha : raw7362step1 = -raw7362step0 := by apply Matrix.ext; change ∀ i j, raw7362step1 i j = -(raw7362step0 i j); unfold raw7362step1 raw7362step0; decide +kernel
      have hl : raw7362step1Labels = raw7362step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7362step1 raw7362step1Labels = mixedMoment B raw7362step2 raw7362step2Labels := by
      have ha : raw7362step2 = raw7362step1 := by apply Matrix.ext; unfold raw7362step2 raw7362step1; decide +kernel
      have hl : raw7362step1Labels = labelEmbedding1 ∘ raw7362step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7362step1 raw7362step1Labels raw7362step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3477 node3477Labels := by rfl

def raw7363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7363Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw7363step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7363step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7363step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7363step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7363step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7363 raw7363Labels = mixedMoment B node3537 node3537Labels := by
  calc
    mixedMoment B raw7363 raw7363Labels = mixedMoment B raw7363step0 raw7363step0Labels := by
      have ha : raw7363step0 = (fun i j => raw7363 (permutation172 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7363step0 raw7363; decide +kernel
      have hl : raw7363step0Labels = raw7363Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7363 raw7363Labels permutation172 permutation7
    mixedMoment B raw7363step0 raw7363step0Labels = mixedMoment B raw7363step1 raw7363step1Labels := by
      have ha : raw7363step1 = -raw7363step0 := by apply Matrix.ext; change ∀ i j, raw7363step1 i j = -(raw7363step0 i j); unfold raw7363step1 raw7363step0; decide +kernel
      have hl : raw7363step1Labels = raw7363step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7363step1 raw7363step1Labels = mixedMoment B raw7363step2 raw7363step2Labels := by
      have ha : raw7363step2 = raw7363step1 := by apply Matrix.ext; unfold raw7363step2 raw7363step1; decide +kernel
      have hl : raw7363step1Labels = labelEmbedding1 ∘ raw7363step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7363step1 raw7363step1Labels raw7363step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3537 node3537Labels := by rfl

def raw7364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7364Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7364step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw7364step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7364step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7364step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7364step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7364step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7364 raw7364Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw7364 raw7364Labels = mixedMoment B raw7364step0 raw7364step0Labels := by
      have ha : raw7364step0 = (fun i j => raw7364 (permutation173 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7364step0 raw7364; decide +kernel
      have hl : raw7364step0Labels = raw7364Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7364 raw7364Labels permutation173 permutation7
    mixedMoment B raw7364step0 raw7364step0Labels = mixedMoment B raw7364step1 raw7364step1Labels := by
      have ha : raw7364step1 = -raw7364step0 := by apply Matrix.ext; change ∀ i j, raw7364step1 i j = -(raw7364step0 i j); unfold raw7364step1 raw7364step0; decide +kernel
      have hl : raw7364step1Labels = raw7364step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7364step1 raw7364step1Labels = mixedMoment B raw7364step2 raw7364step2Labels := by
      have ha : raw7364step2 = raw7364step1 := by apply Matrix.ext; unfold raw7364step2 raw7364step1; decide +kernel
      have hl : raw7364step1Labels = labelEmbedding1 ∘ raw7364step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7364step1 raw7364step1Labels raw7364step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

def raw7365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7365Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7365step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw7365step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7365step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7365step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7365step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7365step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7365 raw7365Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw7365 raw7365Labels = mixedMoment B raw7365step0 raw7365step0Labels := by
      have ha : raw7365step0 = (fun i j => raw7365 (permutation172 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7365step0 raw7365; decide +kernel
      have hl : raw7365step0Labels = raw7365Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7365 raw7365Labels permutation172 permutation7
    mixedMoment B raw7365step0 raw7365step0Labels = mixedMoment B raw7365step1 raw7365step1Labels := by
      have ha : raw7365step1 = -raw7365step0 := by apply Matrix.ext; change ∀ i j, raw7365step1 i j = -(raw7365step0 i j); unfold raw7365step1 raw7365step0; decide +kernel
      have hl : raw7365step1Labels = raw7365step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7365step1 raw7365step1Labels = mixedMoment B raw7365step2 raw7365step2Labels := by
      have ha : raw7365step2 = raw7365step1 := by apply Matrix.ext; unfold raw7365step2 raw7365step1; decide +kernel
      have hl : raw7365step1Labels = labelEmbedding1 ∘ raw7365step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7365step1 raw7365step1Labels raw7365step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

def raw7366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7366Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7366step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw7366step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7366step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7366step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7366step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw7366step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7366 raw7366Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw7366 raw7366Labels = mixedMoment B raw7366step0 raw7366step0Labels := by
      have ha : raw7366step0 = (fun i j => raw7366 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7366step0 raw7366; decide +kernel
      have hl : raw7366step0Labels = raw7366Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7366 raw7366Labels permutation184 permutation5
    mixedMoment B raw7366step0 raw7366step0Labels = mixedMoment B raw7366step1 raw7366step1Labels := by
      have ha : raw7366step1 = -raw7366step0 := by apply Matrix.ext; change ∀ i j, raw7366step1 i j = -(raw7366step0 i j); unfold raw7366step1 raw7366step0; decide +kernel
      have hl : raw7366step1Labels = raw7366step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7366step1 raw7366step1Labels = mixedMoment B raw7366step2 raw7366step2Labels := by
      have ha : raw7366step2 = raw7366step1 := by apply Matrix.ext; unfold raw7366step2 raw7366step1; decide +kernel
      have hl : raw7366step1Labels = labelEmbedding1 ∘ raw7366step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7366step1 raw7366step1Labels raw7366step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3288 node3288Labels := by rfl

def raw7367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7367Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw7367step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7367step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7367step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7367step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7367step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7367 raw7367Labels = mixedMoment B node3477 node3477Labels := by
  calc
    mixedMoment B raw7367 raw7367Labels = mixedMoment B raw7367step0 raw7367step0Labels := by
      have ha : raw7367step0 = (fun i j => raw7367 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7367step0 raw7367; decide +kernel
      have hl : raw7367step0Labels = raw7367Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7367 raw7367Labels permutation170 permutation7
    mixedMoment B raw7367step0 raw7367step0Labels = mixedMoment B raw7367step1 raw7367step1Labels := by
      have ha : raw7367step1 = -raw7367step0 := by apply Matrix.ext; change ∀ i j, raw7367step1 i j = -(raw7367step0 i j); unfold raw7367step1 raw7367step0; decide +kernel
      have hl : raw7367step1Labels = raw7367step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7367step1 raw7367step1Labels = mixedMoment B raw7367step2 raw7367step2Labels := by
      have ha : raw7367step2 = raw7367step1 := by apply Matrix.ext; unfold raw7367step2 raw7367step1; decide +kernel
      have hl : raw7367step1Labels = labelEmbedding1 ∘ raw7367step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7367step1 raw7367step1Labels raw7367step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3477 node3477Labels := by rfl

def raw7368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7368Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw7368step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7368step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7368step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7368step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7368step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7368 raw7368Labels = mixedMoment B node3537 node3537Labels := by
  calc
    mixedMoment B raw7368 raw7368Labels = mixedMoment B raw7368step0 raw7368step0Labels := by
      have ha : raw7368step0 = (fun i j => raw7368 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7368step0 raw7368; decide +kernel
      have hl : raw7368step0Labels = raw7368Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7368 raw7368Labels permutation170 permutation7
    mixedMoment B raw7368step0 raw7368step0Labels = mixedMoment B raw7368step1 raw7368step1Labels := by
      have ha : raw7368step1 = -raw7368step0 := by apply Matrix.ext; change ∀ i j, raw7368step1 i j = -(raw7368step0 i j); unfold raw7368step1 raw7368step0; decide +kernel
      have hl : raw7368step1Labels = raw7368step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7368step1 raw7368step1Labels = mixedMoment B raw7368step2 raw7368step2Labels := by
      have ha : raw7368step2 = raw7368step1 := by apply Matrix.ext; unfold raw7368step2 raw7368step1; decide +kernel
      have hl : raw7368step1Labels = labelEmbedding1 ∘ raw7368step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7368step1 raw7368step1Labels raw7368step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3537 node3537Labels := by rfl

def raw7369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7369Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw7369step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7369step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7369step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7369step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw7369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7369 raw7369Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw7369 raw7369Labels = mixedMoment B raw7369step0 raw7369step0Labels := by
      have ha : raw7369step0 = (fun i j => raw7369 (permutation171 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7369step0 raw7369; decide +kernel
      have hl : raw7369step0Labels = raw7369Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7369 raw7369Labels permutation171 permutation7
    mixedMoment B raw7369step0 raw7369step0Labels = mixedMoment B raw7369step1 raw7369step1Labels := by
      have ha : raw7369step1 = -raw7369step0 := by apply Matrix.ext; change ∀ i j, raw7369step1 i j = -(raw7369step0 i j); unfold raw7369step1 raw7369step0; decide +kernel
      have hl : raw7369step1Labels = raw7369step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7369step1 raw7369step1Labels = mixedMoment B raw7369step2 raw7369step2Labels := by
      have ha : raw7369step2 = raw7369step1 := by apply Matrix.ext; unfold raw7369step2 raw7369step1; decide +kernel
      have hl : raw7369step1Labels = labelEmbedding1 ∘ raw7369step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7369step1 raw7369step1Labels raw7369step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

def raw7370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7370Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw7370step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7370step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7370step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7370 raw7370Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw7370 raw7370Labels = mixedMoment B raw7370step0 raw7370step0Labels := by
      have ha : raw7370step0 = (fun i j => raw7370 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7370step0 raw7370; decide +kernel
      have hl : raw7370step0Labels = raw7370Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7370 raw7370Labels permutation170 permutation7
    mixedMoment B raw7370step0 raw7370step0Labels = mixedMoment B raw7370step1 raw7370step1Labels := by
      have ha : raw7370step1 = -raw7370step0 := by apply Matrix.ext; change ∀ i j, raw7370step1 i j = -(raw7370step0 i j); unfold raw7370step1 raw7370step0; decide +kernel
      have hl : raw7370step1Labels = raw7370step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7370step1 raw7370step1Labels = mixedMoment B raw7370step2 raw7370step2Labels := by
      have ha : raw7370step2 = raw7370step1 := by apply Matrix.ext; unfold raw7370step2 raw7370step1; decide +kernel
      have hl : raw7370step1Labels = labelEmbedding1 ∘ raw7370step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7370step1 raw7370step1Labels raw7370step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

def raw7371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7371Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw7371step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7371step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw7371step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7371step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw7371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7371 raw7371Labels = mixedMoment B node3280 node3280Labels := by
  calc
    mixedMoment B raw7371 raw7371Labels = mixedMoment B raw7371step0 raw7371step0Labels := by
      have ha : raw7371step0 = (fun i j => raw7371 (permutation182 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7371step0 raw7371; decide +kernel
      have hl : raw7371step0Labels = raw7371Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7371 raw7371Labels permutation182 permutation5
    mixedMoment B raw7371step0 raw7371step0Labels = mixedMoment B raw7371step1 raw7371step1Labels := by
      have ha : raw7371step1 = -raw7371step0 := by apply Matrix.ext; change ∀ i j, raw7371step1 i j = -(raw7371step0 i j); unfold raw7371step1 raw7371step0; decide +kernel
      have hl : raw7371step1Labels = raw7371step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7371step1 raw7371step1Labels = mixedMoment B raw7371step2 raw7371step2Labels := by
      have ha : raw7371step2 = raw7371step1 := by apply Matrix.ext; unfold raw7371step2 raw7371step1; decide +kernel
      have hl : raw7371step1Labels = labelEmbedding1 ∘ raw7371step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7371step1 raw7371step1Labels raw7371step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3280 node3280Labels := by rfl

def raw7372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7372Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw7372step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7372step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7372step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7372step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7372 raw7372Labels = mixedMoment B node3476 node3476Labels := by
  calc
    mixedMoment B raw7372 raw7372Labels = mixedMoment B raw7372step0 raw7372step0Labels := by
      have ha : raw7372step0 = (fun i j => raw7372 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7372step0 raw7372; decide +kernel
      have hl : raw7372step0Labels = raw7372Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7372 raw7372Labels permutation170 permutation7
    mixedMoment B raw7372step0 raw7372step0Labels = mixedMoment B raw7372step1 raw7372step1Labels := by
      have ha : raw7372step1 = -raw7372step0 := by apply Matrix.ext; change ∀ i j, raw7372step1 i j = -(raw7372step0 i j); unfold raw7372step1 raw7372step0; decide +kernel
      have hl : raw7372step1Labels = raw7372step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7372step1 raw7372step1Labels = mixedMoment B raw7372step2 raw7372step2Labels := by
      have ha : raw7372step2 = raw7372step1 := by apply Matrix.ext; unfold raw7372step2 raw7372step1; decide +kernel
      have hl : raw7372step1Labels = labelEmbedding1 ∘ raw7372step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7372step1 raw7372step1Labels raw7372step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3476 node3476Labels := by rfl

def raw7373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7373Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw7373step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7373step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7373step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7373 raw7373Labels = mixedMoment B node3536 node3536Labels := by
  calc
    mixedMoment B raw7373 raw7373Labels = mixedMoment B raw7373step0 raw7373step0Labels := by
      have ha : raw7373step0 = (fun i j => raw7373 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7373step0 raw7373; decide +kernel
      have hl : raw7373step0Labels = raw7373Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7373 raw7373Labels permutation170 permutation7
    mixedMoment B raw7373step0 raw7373step0Labels = mixedMoment B raw7373step1 raw7373step1Labels := by
      have ha : raw7373step1 = -raw7373step0 := by apply Matrix.ext; change ∀ i j, raw7373step1 i j = -(raw7373step0 i j); unfold raw7373step1 raw7373step0; decide +kernel
      have hl : raw7373step1Labels = raw7373step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7373step1 raw7373step1Labels = mixedMoment B raw7373step2 raw7373step2Labels := by
      have ha : raw7373step2 = raw7373step1 := by apply Matrix.ext; unfold raw7373step2 raw7373step1; decide +kernel
      have hl : raw7373step1Labels = labelEmbedding1 ∘ raw7373step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7373step1 raw7373step1Labels raw7373step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3536 node3536Labels := by rfl

def raw7374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7374Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw7374step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7374step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7374step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7374step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7374 raw7374Labels = mixedMoment B node3536 node3536Labels := by
  calc
    mixedMoment B raw7374 raw7374Labels = mixedMoment B raw7374step0 raw7374step0Labels := by
      have ha : raw7374step0 = (fun i j => raw7374 (permutation172 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7374step0 raw7374; decide +kernel
      have hl : raw7374step0Labels = raw7374Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7374 raw7374Labels permutation172 permutation7
    mixedMoment B raw7374step0 raw7374step0Labels = mixedMoment B raw7374step1 raw7374step1Labels := by
      have ha : raw7374step1 = -raw7374step0 := by apply Matrix.ext; change ∀ i j, raw7374step1 i j = -(raw7374step0 i j); unfold raw7374step1 raw7374step0; decide +kernel
      have hl : raw7374step1Labels = raw7374step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7374step1 raw7374step1Labels = mixedMoment B raw7374step2 raw7374step2Labels := by
      have ha : raw7374step2 = raw7374step1 := by apply Matrix.ext; unfold raw7374step2 raw7374step1; decide +kernel
      have hl : raw7374step1Labels = labelEmbedding1 ∘ raw7374step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7374step1 raw7374step1Labels raw7374step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3536 node3536Labels := by rfl

def raw7375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw7375Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw7375step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7375step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7375step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7375step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7375 raw7375Labels = mixedMoment B node3531 node3531Labels := by
  calc
    mixedMoment B raw7375 raw7375Labels = mixedMoment B raw7375step0 raw7375step0Labels := by
      have ha : raw7375step0 = (fun i j => raw7375 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7375step0 raw7375; decide +kernel
      have hl : raw7375step0Labels = raw7375Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7375 raw7375Labels permutation170 permutation7
    mixedMoment B raw7375step0 raw7375step0Labels = mixedMoment B raw7375step1 raw7375step1Labels := by
      have ha : raw7375step1 = -raw7375step0 := by apply Matrix.ext; change ∀ i j, raw7375step1 i j = -(raw7375step0 i j); unfold raw7375step1 raw7375step0; decide +kernel
      have hl : raw7375step1Labels = raw7375step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw7375step1 raw7375step1Labels = mixedMoment B raw7375step2 raw7375step2Labels := by
      have ha : raw7375step2 = raw7375step1 := by apply Matrix.ext; unfold raw7375step2 raw7375step1; decide +kernel
      have hl : raw7375step1Labels = labelEmbedding1 ∘ raw7375step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7375step1 raw7375step1Labels raw7375step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3531 node3531Labels := by rfl

def raw7376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw7376Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw7376step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7376step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw7376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7376 raw7376Labels = mixedMoment B node1995 node1995Labels := by
  calc
    mixedMoment B raw7376 raw7376Labels = mixedMoment B raw7376step0 raw7376step0Labels := by
      have ha : raw7376step0 = (fun i j => raw7376 (permutation620 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7376step0 raw7376; decide +kernel
      have hl : raw7376step0Labels = raw7376Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7376 raw7376Labels permutation620 permutation5
    mixedMoment B raw7376step0 raw7376step0Labels = mixedMoment B raw7376step1 raw7376step1Labels := by
      have ha : raw7376step1 = raw7376step0 := by apply Matrix.ext; unfold raw7376step1 raw7376step0; decide +kernel
      have hl : raw7376step0Labels = labelEmbedding1 ∘ raw7376step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7376step0 raw7376step0Labels raw7376step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1995 node1995Labels := by rfl

def raw7377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw7377Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7377step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7377 raw7377Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw7377 raw7377Labels = mixedMoment B raw7377step0 raw7377step0Labels := by
      have ha : raw7377step0 = (fun i j => raw7377 (permutation674 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7377step0 raw7377; decide +kernel
      have hl : raw7377step0Labels = raw7377Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7377 raw7377Labels permutation674 permutation5
    mixedMoment B raw7377step0 raw7377step0Labels = mixedMoment B raw7377step1 raw7377step1Labels := by
      have ha : raw7377step1 = raw7377step0 := by apply Matrix.ext; unfold raw7377step1 raw7377step0; decide +kernel
      have hl : raw7377step0Labels = labelEmbedding1 ∘ raw7377step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7377step0 raw7377step0Labels raw7377step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2201 node2201Labels := by rfl

def raw7378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw7378Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw7378step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7378step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw7378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7378 raw7378Labels = mixedMoment B node1998 node1998Labels := by
  calc
    mixedMoment B raw7378 raw7378Labels = mixedMoment B raw7378step0 raw7378step0Labels := by
      have ha : raw7378step0 = (fun i j => raw7378 (permutation621 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7378step0 raw7378; decide +kernel
      have hl : raw7378step0Labels = raw7378Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7378 raw7378Labels permutation621 permutation5
    mixedMoment B raw7378step0 raw7378step0Labels = mixedMoment B raw7378step1 raw7378step1Labels := by
      have ha : raw7378step1 = raw7378step0 := by apply Matrix.ext; unfold raw7378step1 raw7378step0; decide +kernel
      have hl : raw7378step0Labels = labelEmbedding1 ∘ raw7378step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7378step0 raw7378step0Labels raw7378step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1998 node1998Labels := by rfl

def raw7379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw7379Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw7379step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw7379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7379 raw7379Labels = mixedMoment B node1998 node1998Labels := by
  calc
    mixedMoment B raw7379 raw7379Labels = mixedMoment B raw7379step0 raw7379step0Labels := by
      have ha : raw7379step0 = (fun i j => raw7379 (permutation619 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7379step0 raw7379; decide +kernel
      have hl : raw7379step0Labels = raw7379Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7379 raw7379Labels permutation619 permutation5
    mixedMoment B raw7379step0 raw7379step0Labels = mixedMoment B raw7379step1 raw7379step1Labels := by
      have ha : raw7379step1 = raw7379step0 := by apply Matrix.ext; unfold raw7379step1 raw7379step0; decide +kernel
      have hl : raw7379step0Labels = labelEmbedding1 ∘ raw7379step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7379step0 raw7379step0Labels raw7379step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1998 node1998Labels := by rfl

def raw7380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw7380Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw7380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7380step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw7380step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw7380step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7380 raw7380Labels = mixedMoment B node2050 node2050Labels := by
  calc
    mixedMoment B raw7380 raw7380Labels = mixedMoment B raw7380step0 raw7380step0Labels := by
      have ha : raw7380step0 = (fun i j => raw7380 (permutation609 i) (permutation5 j)) := by apply Matrix.ext; unfold raw7380step0 raw7380; decide +kernel
      have hl : raw7380step0Labels = raw7380Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7380 raw7380Labels permutation609 permutation5
    mixedMoment B raw7380step0 raw7380step0Labels = mixedMoment B raw7380step1 raw7380step1Labels := by
      have ha : raw7380step1 = raw7380step0 := by apply Matrix.ext; unfold raw7380step1 raw7380step0; decide +kernel
      have hl : raw7380step0Labels = labelEmbedding1 ∘ raw7380step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7380step0 raw7380step0Labels raw7380step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2050 node2050Labels := by rfl

def raw7381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7381 raw7381Labels = mixedMoment B node2710 node2710Labels := by
  calc
    _ = mixedMoment B node2710 node2710Labels := by rfl

def raw7382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7382Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7382 raw7382Labels = mixedMoment B node3801 node3801Labels := by
  calc
    _ = mixedMoment B node3801 node3801Labels := by rfl

def raw7383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7383Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7383 raw7383Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw7383 raw7383Labels = mixedMoment B raw7383step0 raw7383step0Labels := by
      have ha : raw7383step0 = (fun i j => raw7383 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7383step0 raw7383; decide +kernel
      have hl : raw7383step0Labels = raw7383Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7383 raw7383Labels permutation176 permutation2
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw7384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7384Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7384step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7384 raw7384Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw7384 raw7384Labels = mixedMoment B raw7384step0 raw7384step0Labels := by
      have ha : raw7384step0 = (fun i j => raw7384 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7384step0 raw7384; decide +kernel
      have hl : raw7384step0Labels = raw7384Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7384 raw7384Labels permutation200 permutation2
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw7385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7385Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7385 raw7385Labels = mixedMoment B node3899 node3899Labels := by
  calc
    _ = mixedMoment B node3899 node3899Labels := by rfl

def raw7386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7386Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw7386step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7386 raw7386Labels = mixedMoment B node3901 node3901Labels := by
  calc
    mixedMoment B raw7386 raw7386Labels = mixedMoment B raw7386step0 raw7386step0Labels := by
      have ha : raw7386step0 = (fun i j => raw7386 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7386step0 raw7386; decide +kernel
      have hl : raw7386step0Labels = raw7386Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7386 raw7386Labels permutation153 permutation2
    _ = mixedMoment B node3901 node3901Labels := by rfl

def raw7387 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]
def raw7387Labels : Fin 2 → Fin 2 := ![0, 1]

def raw7387step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw7387step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical7387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7387 raw7387Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw7387 raw7387Labels = mixedMoment B raw7387step0 raw7387step0Labels := by
      have hz : ∀ j, raw7387 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw7387step0 = (fun i j => raw7387 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw7387step0 raw7387; decide +kernel
      have hl : raw7387step0Labels = raw7387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7387 raw7387Labels permutation590 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw7388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7388Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw7388step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7388 raw7388Labels = mixedMoment B node1248 node1248Labels := by
  calc
    mixedMoment B raw7388 raw7388Labels = mixedMoment B raw7388step0 raw7388step0Labels := by
      have ha : raw7388step0 = (fun i j => raw7388 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7388step0 raw7388; decide +kernel
      have hl : raw7388step0Labels = raw7388Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7388 raw7388Labels permutation182 permutation2
    _ = mixedMoment B node1248 node1248Labels := by rfl

def raw7389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7389Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7389step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7389 raw7389Labels = mixedMoment B node1216 node1216Labels := by
  calc
    mixedMoment B raw7389 raw7389Labels = mixedMoment B raw7389step0 raw7389step0Labels := by
      have ha : raw7389step0 = (fun i j => raw7389 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7389step0 raw7389; decide +kernel
      have hl : raw7389step0Labels = raw7389Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7389 raw7389Labels permutation158 permutation2
    _ = mixedMoment B node1216 node1216Labels := by rfl

def raw7390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7390Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7390 raw7390Labels = mixedMoment B node1216 node1216Labels := by
  calc
    _ = mixedMoment B node1216 node1216Labels := by rfl

def raw7391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7391Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7391step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7391 raw7391Labels = mixedMoment B node1208 node1208Labels := by
  calc
    mixedMoment B raw7391 raw7391Labels = mixedMoment B raw7391step0 raw7391step0Labels := by
      have ha : raw7391step0 = (fun i j => raw7391 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7391step0 raw7391; decide +kernel
      have hl : raw7391step0Labels = raw7391Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7391 raw7391Labels permutation153 permutation2
    _ = mixedMoment B node1208 node1208Labels := by rfl

def raw7392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw7392Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7392 raw7392Labels = mixedMoment B node1207 node1207Labels := by
  calc
    _ = mixedMoment B node1207 node1207Labels := by rfl

def raw7393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7393Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw7393step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7393 raw7393Labels = mixedMoment B node2623 node2623Labels := by
  calc
    mixedMoment B raw7393 raw7393Labels = mixedMoment B raw7393step0 raw7393step0Labels := by
      have ha : raw7393step0 = (fun i j => raw7393 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7393step0 raw7393; decide +kernel
      have hl : raw7393step0Labels = raw7393Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7393 raw7393Labels permutation182 permutation2
    _ = mixedMoment B node2623 node2623Labels := by rfl

def raw7394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7394Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw7394step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7394 raw7394Labels = mixedMoment B node2623 node2623Labels := by
  calc
    mixedMoment B raw7394 raw7394Labels = mixedMoment B raw7394step0 raw7394step0Labels := by
      have ha : raw7394step0 = (fun i j => raw7394 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7394step0 raw7394; decide +kernel
      have hl : raw7394step0Labels = raw7394Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7394 raw7394Labels permutation206 permutation2
    _ = mixedMoment B node2623 node2623Labels := by rfl

def raw7395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7395Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw7395step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7395 raw7395Labels = mixedMoment B node2745 node2745Labels := by
  calc
    mixedMoment B raw7395 raw7395Labels = mixedMoment B raw7395step0 raw7395step0Labels := by
      have ha : raw7395step0 = (fun i j => raw7395 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7395step0 raw7395; decide +kernel
      have hl : raw7395step0Labels = raw7395Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7395 raw7395Labels permutation184 permutation2
    _ = mixedMoment B node2745 node2745Labels := by rfl

def raw7396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7396Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw7396step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7396 raw7396Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw7396 raw7396Labels = mixedMoment B raw7396step0 raw7396step0Labels := by
      have ha : raw7396step0 = (fun i j => raw7396 (permutation183 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7396step0 raw7396; decide +kernel
      have hl : raw7396step0Labels = raw7396Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7396 raw7396Labels permutation183 permutation2
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw7397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7397Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7397 raw7397Labels = mixedMoment B node2483 node2483Labels := by
  calc
    mixedMoment B raw7397 raw7397Labels = mixedMoment B raw7397step0 raw7397step0Labels := by
      have ha : raw7397step0 = (fun i j => raw7397 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7397step0 raw7397; decide +kernel
      have hl : raw7397step0Labels = raw7397Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7397 raw7397Labels permutation158 permutation2
    _ = mixedMoment B node2483 node2483Labels := by rfl

def raw7398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7398Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7398 raw7398Labels = mixedMoment B node2483 node2483Labels := by
  calc
    _ = mixedMoment B node2483 node2483Labels := by rfl

def raw7399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7399Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7399step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7399 raw7399Labels = mixedMoment B node2473 node2473Labels := by
  calc
    mixedMoment B raw7399 raw7399Labels = mixedMoment B raw7399step0 raw7399step0Labels := by
      have ha : raw7399step0 = (fun i j => raw7399 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7399step0 raw7399; decide +kernel
      have hl : raw7399step0Labels = raw7399Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7399 raw7399Labels permutation153 permutation2
    _ = mixedMoment B node2473 node2473Labels := by rfl

def raw7400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw7400Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7400 raw7400Labels = mixedMoment B node2471 node2471Labels := by
  calc
    _ = mixedMoment B node2471 node2471Labels := by rfl

def raw7401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7401Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7401 raw7401Labels = mixedMoment B node2617 node2617Labels := by
  calc
    mixedMoment B raw7401 raw7401Labels = mixedMoment B raw7401step0 raw7401step0Labels := by
      have ha : raw7401step0 = (fun i j => raw7401 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7401step0 raw7401; decide +kernel
      have hl : raw7401step0Labels = raw7401Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7401 raw7401Labels permutation200 permutation2
    _ = mixedMoment B node2617 node2617Labels := by rfl

def raw7402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7402Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7402step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7402 raw7402Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw7402 raw7402Labels = mixedMoment B raw7402step0 raw7402step0Labels := by
      have ha : raw7402step0 = (fun i j => raw7402 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7402step0 raw7402; decide +kernel
      have hl : raw7402step0Labels = raw7402Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7402 raw7402Labels permutation160 permutation2
    _ = mixedMoment B node2710 node2710Labels := by rfl

def raw7403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw7403Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw7403step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7403 raw7403Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw7403 raw7403Labels = mixedMoment B raw7403step0 raw7403step0Labels := by
      have ha : raw7403step0 = (fun i j => raw7403 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7403step0 raw7403; decide +kernel
      have hl : raw7403step0Labels = raw7403Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7403 raw7403Labels permutation162 permutation2
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw7404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7404Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7404step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7404step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7404 raw7404Labels = mixedMoment B node2617 node2617Labels := by
  calc
    mixedMoment B raw7404 raw7404Labels = mixedMoment B raw7404step0 raw7404step0Labels := by
      have ha : raw7404step0 = (fun i j => raw7404 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7404step0 raw7404; decide +kernel
      have hl : raw7404step0Labels = raw7404Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7404 raw7404Labels permutation176 permutation2
    _ = mixedMoment B node2617 node2617Labels := by rfl

def raw7405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw7405Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw7405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7405 raw7405Labels = mixedMoment B node2612 node2612Labels := by
  calc
    mixedMoment B raw7405 raw7405Labels = mixedMoment B raw7405step0 raw7405step0Labels := by
      have ha : raw7405step0 = (fun i j => raw7405 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7405step0 raw7405; decide +kernel
      have hl : raw7405step0Labels = raw7405Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7405 raw7405Labels permutation177 permutation2
    _ = mixedMoment B node2612 node2612Labels := by rfl

def raw7406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw7406Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw7406step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7406 raw7406Labels = mixedMoment B node2611 node2611Labels := by
  calc
    mixedMoment B raw7406 raw7406Labels = mixedMoment B raw7406step0 raw7406step0Labels := by
      have ha : raw7406step0 = (fun i j => raw7406 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7406step0 raw7406; decide +kernel
      have hl : raw7406step0Labels = raw7406Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7406 raw7406Labels permutation176 permutation2
    _ = mixedMoment B node2611 node2611Labels := by rfl

def raw7407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw7407Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw7407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw7407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7407 raw7407Labels = mixedMoment B node2710 node2710Labels := by
  calc
    mixedMoment B raw7407 raw7407Labels = mixedMoment B raw7407step0 raw7407step0Labels := by
      have ha : raw7407step0 = (fun i j => raw7407 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7407step0 raw7407; decide +kernel
      have hl : raw7407step0Labels = raw7407Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7407 raw7407Labels permutation154 permutation2
    _ = mixedMoment B node2710 node2710Labels := by rfl

def raw7408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw7408Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical7408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7408 raw7408Labels = mixedMoment B node2707 node2707Labels := by
  calc
    _ = mixedMoment B node2707 node2707Labels := by rfl

def raw7409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7409Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw7409step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7409step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw7409step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7409 raw7409Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw7409 raw7409Labels = mixedMoment B raw7409step0 raw7409step0Labels := by
      have ha : raw7409step0 = (fun i j => raw7409 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7409step0 raw7409; decide +kernel
      have hl : raw7409step0Labels = raw7409Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7409 raw7409Labels permutation682 permutation2
    mixedMoment B raw7409step0 raw7409step0Labels = mixedMoment B raw7409step1 raw7409step1Labels := by
      have ha : raw7409step1 = -raw7409step0 := by apply Matrix.ext; change ∀ i j, raw7409step1 i j = -(raw7409step0 i j); unfold raw7409step1 raw7409step0; decide +kernel
      have hl : raw7409step1Labels = raw7409step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw7410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7410Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw7410step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7410step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7410step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7410 raw7410Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw7410 raw7410Labels = mixedMoment B raw7410step0 raw7410step0Labels := by
      have ha : raw7410step0 = (fun i j => raw7410 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7410step0 raw7410; decide +kernel
      have hl : raw7410step0Labels = raw7410Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7410 raw7410Labels permutation676 permutation2
    mixedMoment B raw7410step0 raw7410step0Labels = mixedMoment B raw7410step1 raw7410step1Labels := by
      have ha : raw7410step1 = -raw7410step0 := by apply Matrix.ext; change ∀ i j, raw7410step1 i j = -(raw7410step0 i j); unfold raw7410step1 raw7410step0; decide +kernel
      have hl : raw7410step1Labels = raw7410step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw7411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7411Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw7411step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7411step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw7411step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7411 raw7411Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw7411 raw7411Labels = mixedMoment B raw7411step0 raw7411step0Labels := by
      have ha : raw7411step0 = (fun i j => raw7411 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw7411step0 raw7411; decide +kernel
      have hl : raw7411step0Labels = raw7411Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7411 raw7411Labels permutation674 permutation2
    mixedMoment B raw7411step0 raw7411step0Labels = mixedMoment B raw7411step1 raw7411step1Labels := by
      have ha : raw7411step1 = -raw7411step0 := by apply Matrix.ext; change ∀ i j, raw7411step1 i j = -(raw7411step0 i j); unfold raw7411step1 raw7411step0; decide +kernel
      have hl : raw7411step1Labels = raw7411step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw7412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7412Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7412step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7412step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw7412step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw7412step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7412 raw7412Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw7412 raw7412Labels = mixedMoment B raw7412step0 raw7412step0Labels := by
      have hz : ∀ j, raw7412 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7412step0 = (fun i j => raw7412 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7412step0 raw7412; decide +kernel
      have hl : raw7412step0Labels = raw7412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7412 raw7412Labels permutation520 hz
    mixedMoment B raw7412step0 raw7412step0Labels = mixedMoment B raw7412step1 raw7412step1Labels := by
      have ha : raw7412step1 = (fun i j => raw7412step0 (permutation137 i) (permutation7 j)) := by apply Matrix.ext; unfold raw7412step1 raw7412step0; decide +kernel
      have hl : raw7412step1Labels = raw7412step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7412step0 raw7412step0Labels permutation137 permutation7
    mixedMoment B raw7412step1 raw7412step1Labels = mixedMoment B raw7412step2 raw7412step2Labels := by
      have ha : raw7412step2 = raw7412step1 := by apply Matrix.ext; unfold raw7412step2 raw7412step1; decide +kernel
      have hl : raw7412step1Labels = labelEmbedding10 ∘ raw7412step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7412step1 raw7412step1Labels raw7412step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw7413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7413Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7413step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw7413step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw7413step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7413 raw7413Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw7413 raw7413Labels = mixedMoment B raw7413step0 raw7413step0Labels := by
      have ha : raw7413step0 = (fun i j => raw7413 (permutation617 i) (permutation6 j)) := by apply Matrix.ext; unfold raw7413step0 raw7413; decide +kernel
      have hl : raw7413step0Labels = raw7413Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7413 raw7413Labels permutation617 permutation6
    mixedMoment B raw7413step0 raw7413step0Labels = mixedMoment B raw7413step1 raw7413step1Labels := by
      have ha : raw7413step1 = raw7413step0 := by apply Matrix.ext; unfold raw7413step1 raw7413step0; decide +kernel
      have hl : raw7413step0Labels = labelEmbedding9 ∘ raw7413step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7413step0 raw7413step0Labels raw7413step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

def raw7414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7414Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7414step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7414step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7414step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7414 raw7414Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw7414 raw7414Labels = mixedMoment B raw7414step0 raw7414step0Labels := by
      have ha : raw7414step0 = (fun i j => raw7414 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7414step0 raw7414; decide +kernel
      have hl : raw7414step0Labels = raw7414Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7414 raw7414Labels permutation182 permutation3
    mixedMoment B raw7414step0 raw7414step0Labels = mixedMoment B raw7414step1 raw7414step1Labels := by
      have ha : raw7414step1 = raw7414step0 := by apply Matrix.ext; unfold raw7414step1 raw7414step0; decide +kernel
      have hl : raw7414step0Labels = labelEmbedding6 ∘ raw7414step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7414step0 raw7414step0Labels raw7414step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4439 node4439Labels := by rfl

def raw7415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7415step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7415step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7415step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7415 raw7415Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw7415 raw7415Labels = mixedMoment B raw7415step0 raw7415step0Labels := by
      have ha : raw7415step0 = (fun i j => raw7415 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7415step0 raw7415; decide +kernel
      have hl : raw7415step0Labels = raw7415Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7415 raw7415Labels permutation182 permutation3
    mixedMoment B raw7415step0 raw7415step0Labels = mixedMoment B raw7415step1 raw7415step1Labels := by
      have ha : raw7415step1 = raw7415step0 := by apply Matrix.ext; unfold raw7415step1 raw7415step0; decide +kernel
      have hl : raw7415step0Labels = labelEmbedding6 ∘ raw7415step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7415step0 raw7415step0Labels raw7415step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw7416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7416step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7416step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw7416step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7416 raw7416Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw7416 raw7416Labels = mixedMoment B raw7416step0 raw7416step0Labels := by
      have ha : raw7416step0 = (fun i j => raw7416 (permutation206 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7416step0 raw7416; decide +kernel
      have hl : raw7416step0Labels = raw7416Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7416 raw7416Labels permutation206 permutation3
    mixedMoment B raw7416step0 raw7416step0Labels = mixedMoment B raw7416step1 raw7416step1Labels := by
      have ha : raw7416step1 = raw7416step0 := by apply Matrix.ext; unfold raw7416step1 raw7416step0; decide +kernel
      have hl : raw7416step0Labels = labelEmbedding6 ∘ raw7416step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7416step0 raw7416step0Labels raw7416step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw7417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7417step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw7417step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7417step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw7417step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7417 raw7417Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw7417 raw7417Labels = mixedMoment B raw7417step0 raw7417step0Labels := by
      have hz : ∀ j, raw7417 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7417step0 = (fun i j => raw7417 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7417step0 raw7417; decide +kernel
      have hl : raw7417step0Labels = raw7417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7417 raw7417Labels permutation520 hz
    mixedMoment B raw7417step0 raw7417step0Labels = mixedMoment B raw7417step1 raw7417step1Labels := by
      have ha : raw7417step1 = (fun i j => raw7417step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7417step1 raw7417step0; decide +kernel
      have hl : raw7417step1Labels = raw7417step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7417step0 raw7417step0Labels permutation40 permutation3
    mixedMoment B raw7417step1 raw7417step1Labels = mixedMoment B raw7417step2 raw7417step2Labels := by
      have ha : raw7417step2 = raw7417step1 := by apply Matrix.ext; unfold raw7417step2 raw7417step1; decide +kernel
      have hl : raw7417step1Labels = labelEmbedding6 ∘ raw7417step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7417step1 raw7417step1Labels raw7417step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw7418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw7418step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw7418step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7418 raw7418Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw7418 raw7418Labels = mixedMoment B raw7418step0 raw7418step0Labels := by
      have ha : raw7418step0 = (fun i j => raw7418 (permutation186 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7418step0 raw7418; decide +kernel
      have hl : raw7418step0Labels = raw7418Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7418 raw7418Labels permutation186 permutation3
    mixedMoment B raw7418step0 raw7418step0Labels = mixedMoment B raw7418step1 raw7418step1Labels := by
      have ha : raw7418step1 = raw7418step0 := by apply Matrix.ext; unfold raw7418step1 raw7418step0; decide +kernel
      have hl : raw7418step0Labels = labelEmbedding6 ∘ raw7418step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7418step0 raw7418step0Labels raw7418step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw7419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7419step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7419step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7419 raw7419Labels = mixedMoment B node4400 node4400Labels := by
  calc
    mixedMoment B raw7419 raw7419Labels = mixedMoment B raw7419step0 raw7419step0Labels := by
      have ha : raw7419step0 = (fun i j => raw7419 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7419step0 raw7419; decide +kernel
      have hl : raw7419step0Labels = raw7419Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7419 raw7419Labels permutation160 permutation3
    mixedMoment B raw7419step0 raw7419step0Labels = mixedMoment B raw7419step1 raw7419step1Labels := by
      have ha : raw7419step1 = raw7419step0 := by apply Matrix.ext; unfold raw7419step1 raw7419step0; decide +kernel
      have hl : raw7419step0Labels = labelEmbedding6 ∘ raw7419step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7419step0 raw7419step0Labels raw7419step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4400 node4400Labels := by rfl

def raw7420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7420step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7420step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7420step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7420 raw7420Labels = mixedMoment B node4999 node4999Labels := by
  calc
    mixedMoment B raw7420 raw7420Labels = mixedMoment B raw7420step0 raw7420step0Labels := by
      have ha : raw7420step0 = (fun i j => raw7420 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7420step0 raw7420; decide +kernel
      have hl : raw7420step0Labels = raw7420Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7420 raw7420Labels permutation160 permutation3
    mixedMoment B raw7420step0 raw7420step0Labels = mixedMoment B raw7420step1 raw7420step1Labels := by
      have ha : raw7420step1 = raw7420step0 := by apply Matrix.ext; unfold raw7420step1 raw7420step0; decide +kernel
      have hl : raw7420step0Labels = labelEmbedding6 ∘ raw7420step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7420step0 raw7420step0Labels raw7420step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4999 node4999Labels := by rfl

def raw7421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw7421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7421step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7421step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7421step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7421 raw7421Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw7421 raw7421Labels = mixedMoment B raw7421step0 raw7421step0Labels := by
      have ha : raw7421step0 = (fun i j => raw7421 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7421step0 raw7421; decide +kernel
      have hl : raw7421step0Labels = raw7421Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7421 raw7421Labels permutation202 permutation3
    mixedMoment B raw7421step0 raw7421step0Labels = mixedMoment B raw7421step1 raw7421step1Labels := by
      have ha : raw7421step1 = raw7421step0 := by apply Matrix.ext; unfold raw7421step1 raw7421step0; decide +kernel
      have hl : raw7421step0Labels = labelEmbedding6 ∘ raw7421step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7421step0 raw7421step0Labels raw7421step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5138 node5138Labels := by rfl

def raw7422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw7422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![2, 0, -2]]
def raw7422step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7422step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw7422step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7422 raw7422Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw7422 raw7422Labels = mixedMoment B raw7422step0 raw7422step0Labels := by
      have hz : ∀ j, raw7422 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw7422step0 = (fun i j => raw7422 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw7422step0 raw7422; decide +kernel
      have hl : raw7422step0Labels = raw7422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw7422 raw7422Labels permutation520 hz
    mixedMoment B raw7422step0 raw7422step0Labels = mixedMoment B raw7422step1 raw7422step1Labels := by
      have ha : raw7422step1 = (fun i j => raw7422step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7422step1 raw7422step0; decide +kernel
      have hl : raw7422step1Labels = raw7422step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7422step0 raw7422step0Labels permutation34 permutation3
    mixedMoment B raw7422step1 raw7422step1Labels = mixedMoment B raw7422step2 raw7422step2Labels := by
      have ha : raw7422step2 = raw7422step1 := by apply Matrix.ext; unfold raw7422step2 raw7422step1; decide +kernel
      have hl : raw7422step1Labels = labelEmbedding6 ∘ raw7422step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7422step1 raw7422step1Labels raw7422step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw7423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw7423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw7423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7423step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw7423step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw7423step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical7423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw7423 raw7423Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw7423 raw7423Labels = mixedMoment B raw7423step0 raw7423step0Labels := by
      have ha : raw7423step0 = (fun i j => raw7423 (permutation163 i) (permutation3 j)) := by apply Matrix.ext; unfold raw7423step0 raw7423; decide +kernel
      have hl : raw7423step0Labels = raw7423Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw7423 raw7423Labels permutation163 permutation3
    mixedMoment B raw7423step0 raw7423step0Labels = mixedMoment B raw7423step1 raw7423step1Labels := by
      have ha : raw7423step1 = raw7423step0 := by apply Matrix.ext; unfold raw7423step1 raw7423step0; decide +kernel
      have hl : raw7423step0Labels = labelEmbedding6 ∘ raw7423step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw7423step0 raw7423step0Labels raw7423step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
