import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw36864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36864step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36864 raw36864Labels = mixedMoment B node5392 node5392Labels := by
  calc
    mixedMoment B raw36864 raw36864Labels = mixedMoment B raw36864step0 raw36864step0Labels := by
      have ha : raw36864step0 = (fun i j => raw36864 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36864step0 raw36864; decide +kernel
      have hl : raw36864step0Labels = raw36864Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36864 raw36864Labels permutation664 permutation2
    mixedMoment B raw36864step0 raw36864step0Labels = mixedMoment B raw36864step1 raw36864step1Labels := by
      have ha : raw36864step1 = -raw36864step0 := by apply Matrix.ext; change ∀ i j, raw36864step1 i j = -(raw36864step0 i j); unfold raw36864step1 raw36864step0; decide +kernel
      have hl : raw36864step1Labels = raw36864step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5392 node5392Labels := by rfl

def raw36865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36865step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36865step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36865step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36865 raw36865Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw36865 raw36865Labels = mixedMoment B raw36865step0 raw36865step0Labels := by
      have ha : raw36865step0 = (fun i j => raw36865 (permutation687 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36865step0 raw36865; decide +kernel
      have hl : raw36865step0Labels = raw36865Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36865 raw36865Labels permutation687 permutation7
    mixedMoment B raw36865step0 raw36865step0Labels = mixedMoment B raw36865step1 raw36865step1Labels := by
      have ha : raw36865step1 = raw36865step0 := by apply Matrix.ext; unfold raw36865step1 raw36865step0; decide +kernel
      have hl : raw36865step0Labels = labelEmbedding10 ∘ raw36865step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36865step0 raw36865step0Labels raw36865step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw36866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw36866Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36866step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36866step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36866step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36866 raw36866Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw36866 raw36866Labels = mixedMoment B raw36866step0 raw36866step0Labels := by
      have ha : raw36866step0 = (fun i j => raw36866 (permutation663 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36866step0 raw36866; decide +kernel
      have hl : raw36866step0Labels = raw36866Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36866 raw36866Labels permutation663 permutation7
    mixedMoment B raw36866step0 raw36866step0Labels = mixedMoment B raw36866step1 raw36866step1Labels := by
      have ha : raw36866step1 = raw36866step0 := by apply Matrix.ext; unfold raw36866step1 raw36866step0; decide +kernel
      have hl : raw36866step0Labels = labelEmbedding10 ∘ raw36866step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36866step0 raw36866step0Labels raw36866step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw36867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36867Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36867step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36867step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36867step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36867step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36867 raw36867Labels = mixedMoment B node5469 node5469Labels := by
  calc
    mixedMoment B raw36867 raw36867Labels = mixedMoment B raw36867step0 raw36867step0Labels := by
      have ha : raw36867step0 = (fun i j => raw36867 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36867step0 raw36867; decide +kernel
      have hl : raw36867step0Labels = raw36867Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36867 raw36867Labels permutation265 permutation7
    mixedMoment B raw36867step0 raw36867step0Labels = mixedMoment B raw36867step1 raw36867step1Labels := by
      have ha : raw36867step1 = -raw36867step0 := by apply Matrix.ext; change ∀ i j, raw36867step1 i j = -(raw36867step0 i j); unfold raw36867step1 raw36867step0; decide +kernel
      have hl : raw36867step1Labels = raw36867step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36867step1 raw36867step1Labels = mixedMoment B raw36867step2 raw36867step2Labels := by
      have ha : raw36867step2 = raw36867step1 := by apply Matrix.ext; unfold raw36867step2 raw36867step1; decide +kernel
      have hl : raw36867step1Labels = labelEmbedding10 ∘ raw36867step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36867step1 raw36867step1Labels raw36867step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5469 node5469Labels := by rfl

def raw36868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36868Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36868step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36868step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36868 raw36868Labels = mixedMoment B node4969 node4969Labels := by
  calc
    mixedMoment B raw36868 raw36868Labels = mixedMoment B raw36868step0 raw36868step0Labels := by
      have ha : raw36868step0 = (fun i j => raw36868 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36868step0 raw36868; decide +kernel
      have hl : raw36868step0Labels = raw36868Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36868 raw36868Labels permutation160 permutation3
    mixedMoment B raw36868step0 raw36868step0Labels = mixedMoment B raw36868step1 raw36868step1Labels := by
      have ha : raw36868step1 = raw36868step0 := by apply Matrix.ext; unfold raw36868step1 raw36868step0; decide +kernel
      have hl : raw36868step0Labels = labelEmbedding6 ∘ raw36868step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36868step0 raw36868step0Labels raw36868step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4969 node4969Labels := by rfl

def raw36869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36869Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36869step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36869 raw36869Labels = mixedMoment B node4936 node4936Labels := by
  calc
    mixedMoment B raw36869 raw36869Labels = mixedMoment B raw36869step0 raw36869step0Labels := by
      have ha : raw36869step0 = (fun i j => raw36869 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36869step0 raw36869; decide +kernel
      have hl : raw36869step0Labels = raw36869Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36869 raw36869Labels permutation265 permutation2
    _ = mixedMoment B node4936 node4936Labels := by rfl

def raw36870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36870Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36870step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36870 raw36870Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw36870 raw36870Labels = mixedMoment B raw36870step0 raw36870step0Labels := by
      have ha : raw36870step0 = (fun i j => raw36870 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36870step0 raw36870; decide +kernel
      have hl : raw36870step0Labels = raw36870Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36870 raw36870Labels permutation271 permutation2
    _ = mixedMoment B node5349 node5349Labels := by rfl

def raw36871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw36871Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36871step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36871 raw36871Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw36871 raw36871Labels = mixedMoment B raw36871step0 raw36871step0Labels := by
      have ha : raw36871step0 = (fun i j => raw36871 (permutation277 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36871step0 raw36871; decide +kernel
      have hl : raw36871step0Labels = raw36871Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36871 raw36871Labels permutation277 permutation2
    _ = mixedMoment B node5349 node5349Labels := by rfl

def raw36872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36872Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36872step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36872 raw36872Labels = mixedMoment B node5363 node5363Labels := by
  calc
    mixedMoment B raw36872 raw36872Labels = mixedMoment B raw36872step0 raw36872step0Labels := by
      have ha : raw36872step0 = (fun i j => raw36872 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36872step0 raw36872; decide +kernel
      have hl : raw36872step0Labels = raw36872Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36872 raw36872Labels permutation265 permutation2
    _ = mixedMoment B node5363 node5363Labels := by rfl

def raw36873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36873Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw36873step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36873step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw36873step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36873 raw36873Labels = mixedMoment B node4961 node4961Labels := by
  calc
    mixedMoment B raw36873 raw36873Labels = mixedMoment B raw36873step0 raw36873step0Labels := by
      have ha : raw36873step0 = (fun i j => raw36873 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36873step0 raw36873; decide +kernel
      have hl : raw36873step0Labels = raw36873Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36873 raw36873Labels permutation155 permutation3
    mixedMoment B raw36873step0 raw36873step0Labels = mixedMoment B raw36873step1 raw36873step1Labels := by
      have ha : raw36873step1 = raw36873step0 := by apply Matrix.ext; unfold raw36873step1 raw36873step0; decide +kernel
      have hl : raw36873step0Labels = labelEmbedding6 ∘ raw36873step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36873step0 raw36873step0Labels raw36873step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4961 node4961Labels := by rfl

def raw36874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36874Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36874step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36874 raw36874Labels = mixedMoment B node4928 node4928Labels := by
  calc
    mixedMoment B raw36874 raw36874Labels = mixedMoment B raw36874step0 raw36874step0Labels := by
      have ha : raw36874step0 = (fun i j => raw36874 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36874step0 raw36874; decide +kernel
      have hl : raw36874step0Labels = raw36874Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36874 raw36874Labels permutation267 permutation2
    _ = mixedMoment B node4928 node4928Labels := by rfl

def raw36875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36875Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36875step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36875 raw36875Labels = mixedMoment B node5332 node5332Labels := by
  calc
    mixedMoment B raw36875 raw36875Labels = mixedMoment B raw36875step0 raw36875step0Labels := by
      have ha : raw36875step0 = (fun i j => raw36875 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36875step0 raw36875; decide +kernel
      have hl : raw36875step0Labels = raw36875Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36875 raw36875Labels permutation267 permutation2
    _ = mixedMoment B node5332 node5332Labels := by rfl

def raw36876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw36876Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36876step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36876 raw36876Labels = mixedMoment B node5341 node5341Labels := by
  calc
    mixedMoment B raw36876 raw36876Labels = mixedMoment B raw36876step0 raw36876step0Labels := by
      have ha : raw36876step0 = (fun i j => raw36876 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36876step0 raw36876; decide +kernel
      have hl : raw36876step0Labels = raw36876Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36876 raw36876Labels permutation267 permutation2
    _ = mixedMoment B node5341 node5341Labels := by rfl

def raw36877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36877Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36877step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36877 raw36877Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw36877 raw36877Labels = mixedMoment B raw36877step0 raw36877step0Labels := by
      have ha : raw36877step0 = (fun i j => raw36877 (permutation268 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36877step0 raw36877; decide +kernel
      have hl : raw36877step0Labels = raw36877Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36877 raw36877Labels permutation268 permutation2
    _ = mixedMoment B node5346 node5346Labels := by rfl

def raw36878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36878Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36878step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw36878step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36878step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw36878step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36878 raw36878Labels = mixedMoment B node4961 node4961Labels := by
  calc
    mixedMoment B raw36878 raw36878Labels = mixedMoment B raw36878step0 raw36878step0Labels := by
      have ha : raw36878step0 = (fun i j => raw36878 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36878step0 raw36878; decide +kernel
      have hl : raw36878step0Labels = raw36878Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36878 raw36878Labels permutation153 permutation3
    mixedMoment B raw36878step0 raw36878step0Labels = mixedMoment B raw36878step1 raw36878step1Labels := by
      have ha : raw36878step1 = raw36878step0 := by apply Matrix.ext; unfold raw36878step1 raw36878step0; decide +kernel
      have hl : raw36878step0Labels = labelEmbedding6 ∘ raw36878step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36878step0 raw36878step0Labels raw36878step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4961 node4961Labels := by rfl

def raw36879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36879Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36879step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36879step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36879 raw36879Labels = mixedMoment B node4928 node4928Labels := by
  calc
    mixedMoment B raw36879 raw36879Labels = mixedMoment B raw36879step0 raw36879step0Labels := by
      have ha : raw36879step0 = (fun i j => raw36879 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36879step0 raw36879; decide +kernel
      have hl : raw36879step0Labels = raw36879Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36879 raw36879Labels permutation265 permutation2
    _ = mixedMoment B node4928 node4928Labels := by rfl

def raw36880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36880Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36880step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36880 raw36880Labels = mixedMoment B node5332 node5332Labels := by
  calc
    mixedMoment B raw36880 raw36880Labels = mixedMoment B raw36880step0 raw36880step0Labels := by
      have ha : raw36880step0 = (fun i j => raw36880 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36880step0 raw36880; decide +kernel
      have hl : raw36880step0Labels = raw36880Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36880 raw36880Labels permutation265 permutation2
    _ = mixedMoment B node5332 node5332Labels := by rfl

def raw36881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36881step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36881 raw36881Labels = mixedMoment B node5341 node5341Labels := by
  calc
    mixedMoment B raw36881 raw36881Labels = mixedMoment B raw36881step0 raw36881step0Labels := by
      have ha : raw36881step0 = (fun i j => raw36881 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36881step0 raw36881; decide +kernel
      have hl : raw36881step0Labels = raw36881Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36881 raw36881Labels permutation265 permutation2
    _ = mixedMoment B node5341 node5341Labels := by rfl

def raw36882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 1, -2]]
def raw36882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36882step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36882 raw36882Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw36882 raw36882Labels = mixedMoment B raw36882step0 raw36882step0Labels := by
      have ha : raw36882step0 = (fun i j => raw36882 (permutation266 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36882step0 raw36882; decide +kernel
      have hl : raw36882step0Labels = raw36882Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36882 raw36882Labels permutation266 permutation2
    _ = mixedMoment B node5346 node5346Labels := by rfl

def raw36883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw36883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36883step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw36883step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36883step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw36883step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36883 raw36883Labels = mixedMoment B node4960 node4960Labels := by
  calc
    mixedMoment B raw36883 raw36883Labels = mixedMoment B raw36883step0 raw36883step0Labels := by
      have ha : raw36883step0 = (fun i j => raw36883 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36883step0 raw36883; decide +kernel
      have hl : raw36883step0Labels = raw36883Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36883 raw36883Labels permutation152 permutation3
    mixedMoment B raw36883step0 raw36883step0Labels = mixedMoment B raw36883step1 raw36883step1Labels := by
      have ha : raw36883step1 = raw36883step0 := by apply Matrix.ext; unfold raw36883step1 raw36883step0; decide +kernel
      have hl : raw36883step0Labels = labelEmbedding6 ∘ raw36883step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36883step0 raw36883step0Labels raw36883step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4960 node4960Labels := by rfl

def raw36884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw36884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36884step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw36884step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36884 raw36884Labels = mixedMoment B node4927 node4927Labels := by
  calc
    mixedMoment B raw36884 raw36884Labels = mixedMoment B raw36884step0 raw36884step0Labels := by
      have ha : raw36884step0 = (fun i j => raw36884 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36884step0 raw36884; decide +kernel
      have hl : raw36884step0Labels = raw36884Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36884 raw36884Labels permutation265 permutation2
    _ = mixedMoment B node4927 node4927Labels := by rfl

def raw36885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw36885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36885step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36885step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36885 raw36885Labels = mixedMoment B node5029 node5029Labels := by
  calc
    mixedMoment B raw36885 raw36885Labels = mixedMoment B raw36885step0 raw36885step0Labels := by
      have ha : raw36885step0 = (fun i j => raw36885 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36885step0 raw36885; decide +kernel
      have hl : raw36885step0Labels = raw36885Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36885 raw36885Labels permutation663 permutation2
    mixedMoment B raw36885step0 raw36885step0Labels = mixedMoment B raw36885step1 raw36885step1Labels := by
      have ha : raw36885step1 = -raw36885step0 := by apply Matrix.ext; change ∀ i j, raw36885step1 i j = -(raw36885step0 i j); unfold raw36885step1 raw36885step0; decide +kernel
      have hl : raw36885step1Labels = raw36885step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5029 node5029Labels := by rfl

def raw36886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw36886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36886step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36886 raw36886Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw36886 raw36886Labels = mixedMoment B raw36886step0 raw36886step0Labels := by
      have ha : raw36886step0 = (fun i j => raw36886 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36886step0 raw36886; decide +kernel
      have hl : raw36886step0Labels = raw36886Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36886 raw36886Labels permutation687 permutation2
    mixedMoment B raw36886step0 raw36886step0Labels = mixedMoment B raw36886step1 raw36886step1Labels := by
      have ha : raw36886step1 = -raw36886step0 := by apply Matrix.ext; change ∀ i j, raw36886step1 i j = -(raw36886step0 i j); unfold raw36886step1 raw36886step0; decide +kernel
      have hl : raw36886step1Labels = raw36886step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5050 node5050Labels := by rfl

def raw36887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -1, -2]]
def raw36887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36887 raw36887Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw36887 raw36887Labels = mixedMoment B raw36887step0 raw36887step0Labels := by
      have ha : raw36887step0 = (fun i j => raw36887 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36887step0 raw36887; decide +kernel
      have hl : raw36887step0Labels = raw36887Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36887 raw36887Labels permutation663 permutation2
    mixedMoment B raw36887step0 raw36887step0Labels = mixedMoment B raw36887step1 raw36887step1Labels := by
      have ha : raw36887step1 = -raw36887step0 := by apply Matrix.ext; change ∀ i j, raw36887step1 i j = -(raw36887step0 i j); unfold raw36887step1 raw36887step0; decide +kernel
      have hl : raw36887step1Labels = raw36887step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5050 node5050Labels := by rfl

def raw36888 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 3, -2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36888step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36888step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36888step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36888step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36888step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36888step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36888 raw36888Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw36888 raw36888Labels = mixedMoment B raw36888step0 raw36888step0Labels := by
      have ha : raw36888step0 = (fun i j => raw36888 (permutation289 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36888step0 raw36888; decide +kernel
      have hl : raw36888step0Labels = raw36888Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36888 raw36888Labels permutation289 permutation4
    mixedMoment B raw36888step0 raw36888step0Labels = mixedMoment B raw36888step1 raw36888step1Labels := by
      have ha : raw36888step1 = -raw36888step0 := by apply Matrix.ext; change ∀ i j, raw36888step1 i j = -(raw36888step0 i j); unfold raw36888step1 raw36888step0; decide +kernel
      have hl : raw36888step1Labels = raw36888step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36888step1 raw36888step1Labels = mixedMoment B raw36888step2 raw36888step2Labels := by
      have ha : raw36888step2 = raw36888step1 := by apply Matrix.ext; unfold raw36888step2 raw36888step1; decide +kernel
      have hl : raw36888step1Labels = labelEmbedding7 ∘ raw36888step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36888step1 raw36888step1Labels raw36888step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

def raw36889 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36889step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36889step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36889step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36889step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36889 raw36889Labels = mixedMoment B node5374 node5374Labels := by
  calc
    mixedMoment B raw36889 raw36889Labels = mixedMoment B raw36889step0 raw36889step0Labels := by
      have ha : raw36889step0 = (fun i j => raw36889 (permutation289 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36889step0 raw36889; decide +kernel
      have hl : raw36889step0Labels = raw36889Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36889 raw36889Labels permutation289 permutation4
    mixedMoment B raw36889step0 raw36889step0Labels = mixedMoment B raw36889step1 raw36889step1Labels := by
      have ha : raw36889step1 = -raw36889step0 := by apply Matrix.ext; change ∀ i j, raw36889step1 i j = -(raw36889step0 i j); unfold raw36889step1 raw36889step0; decide +kernel
      have hl : raw36889step1Labels = raw36889step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36889step1 raw36889step1Labels = mixedMoment B raw36889step2 raw36889step2Labels := by
      have ha : raw36889step2 = raw36889step1 := by apply Matrix.ext; unfold raw36889step2 raw36889step1; decide +kernel
      have hl : raw36889step1Labels = labelEmbedding7 ∘ raw36889step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36889step1 raw36889step1Labels raw36889step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5374 node5374Labels := by rfl

def raw36890 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36890step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36890 raw36890Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw36890 raw36890Labels = mixedMoment B raw36890step0 raw36890step0Labels := by
      have ha : raw36890step0 = (fun i j => raw36890 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36890step0 raw36890; decide +kernel
      have hl : raw36890step0Labels = raw36890Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36890 raw36890Labels permutation265 permutation6
    mixedMoment B raw36890step0 raw36890step0Labels = mixedMoment B raw36890step1 raw36890step1Labels := by
      have ha : raw36890step1 = raw36890step0 := by apply Matrix.ext; unfold raw36890step1 raw36890step0; decide +kernel
      have hl : raw36890step0Labels = labelEmbedding9 ∘ raw36890step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36890step0 raw36890step0Labels raw36890step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw36891 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw36891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36891step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36891 raw36891Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw36891 raw36891Labels = mixedMoment B raw36891step0 raw36891step0Labels := by
      have ha : raw36891step0 = (fun i j => raw36891 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36891step0 raw36891; decide +kernel
      have hl : raw36891step0Labels = raw36891Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36891 raw36891Labels permutation265 permutation6
    mixedMoment B raw36891step0 raw36891step0Labels = mixedMoment B raw36891step1 raw36891step1Labels := by
      have ha : raw36891step1 = raw36891step0 := by apply Matrix.ext; unfold raw36891step1 raw36891step0; decide +kernel
      have hl : raw36891step0Labels = labelEmbedding9 ∘ raw36891step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36891step0 raw36891step0Labels raw36891step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw36892 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw36892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36892step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36892step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36892step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36892step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36892step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36892step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36892 raw36892Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw36892 raw36892Labels = mixedMoment B raw36892step0 raw36892step0Labels := by
      have ha : raw36892step0 = (fun i j => raw36892 (permutation663 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36892step0 raw36892; decide +kernel
      have hl : raw36892step0Labels = raw36892Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36892 raw36892Labels permutation663 permutation6
    mixedMoment B raw36892step0 raw36892step0Labels = mixedMoment B raw36892step1 raw36892step1Labels := by
      have ha : raw36892step1 = -raw36892step0 := by apply Matrix.ext; change ∀ i j, raw36892step1 i j = -(raw36892step0 i j); unfold raw36892step1 raw36892step0; decide +kernel
      have hl : raw36892step1Labels = raw36892step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36892step1 raw36892step1Labels = mixedMoment B raw36892step2 raw36892step2Labels := by
      have ha : raw36892step2 = raw36892step1 := by apply Matrix.ext; unfold raw36892step2 raw36892step1; decide +kernel
      have hl : raw36892step1Labels = labelEmbedding9 ∘ raw36892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36892step1 raw36892step1Labels raw36892step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw36893 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36893step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw36893step1Labels : Fin 2 → Fin 3 := ![1, 2]

def raw36893step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw36893step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw36893step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw36893step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical36893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36893 raw36893Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw36893 raw36893Labels = mixedMoment B raw36893step0 raw36893step0Labels := by
      have hz : ∀ j, raw36893 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36893step0 = (fun i j => raw36893 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36893step0 raw36893; decide +kernel
      have hl : raw36893step0Labels = raw36893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36893 raw36893Labels permutation346 hz
    mixedMoment B raw36893step0 raw36893step0Labels = mixedMoment B raw36893step1 raw36893step1Labels := by
      have hz : ∀ i, raw36893step0 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw36893step1 = (fun i j => raw36893step0 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw36893step1 raw36893step0; decide +kernel
      have hl : raw36893step1Labels = (fun j => raw36893step0Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw36893step0 raw36893step0Labels permutation2 hz
    mixedMoment B raw36893step1 raw36893step1Labels = mixedMoment B raw36893step2 raw36893step2Labels := by
      have ha : raw36893step2 = -raw36893step1 := by apply Matrix.ext; change ∀ i j, raw36893step2 i j = -(raw36893step1 i j); unfold raw36893step2 raw36893step1; decide +kernel
      have hl : raw36893step2Labels = raw36893step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36893step2 raw36893step2Labels = mixedMoment B raw36893step3 raw36893step3Labels := by
      have ha : raw36893step3 = raw36893step2 := by apply Matrix.ext; unfold raw36893step3 raw36893step2; decide +kernel
      have hl : raw36893step2Labels = labelEmbedding3 ∘ raw36893step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36893step2 raw36893step2Labels raw36893step3Labels labelEmbedding3 hl
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw36894 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36894step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36894step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36894step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36894step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36894 raw36894Labels = mixedMoment B node5017 node5017Labels := by
  calc
    mixedMoment B raw36894 raw36894Labels = mixedMoment B raw36894step0 raw36894step0Labels := by
      have hz : ∀ j, raw36894 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36894step0 = (fun i j => raw36894 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36894step0 raw36894; decide +kernel
      have hl : raw36894step0Labels = raw36894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36894 raw36894Labels permutation346 hz
    mixedMoment B raw36894step0 raw36894step0Labels = mixedMoment B raw36894step1 raw36894step1Labels := by
      have ha : raw36894step1 = (fun i j => raw36894step0 (permutation56 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36894step1 raw36894step0; decide +kernel
      have hl : raw36894step1Labels = raw36894step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36894step0 raw36894step0Labels permutation56 permutation4
    mixedMoment B raw36894step1 raw36894step1Labels = mixedMoment B raw36894step2 raw36894step2Labels := by
      have ha : raw36894step2 = -raw36894step1 := by apply Matrix.ext; change ∀ i j, raw36894step2 i j = -(raw36894step1 i j); unfold raw36894step2 raw36894step1; decide +kernel
      have hl : raw36894step2Labels = raw36894step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36894step2 raw36894step2Labels = mixedMoment B raw36894step3 raw36894step3Labels := by
      have ha : raw36894step3 = raw36894step2 := by apply Matrix.ext; unfold raw36894step3 raw36894step2; decide +kernel
      have hl : raw36894step2Labels = labelEmbedding7 ∘ raw36894step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36894step2 raw36894step2Labels raw36894step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5017 node5017Labels := by rfl

def raw36895 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36895step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36895step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36895step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36895step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36895step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36895 raw36895Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw36895 raw36895Labels = mixedMoment B raw36895step0 raw36895step0Labels := by
      have hz : ∀ j, raw36895 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36895step0 = (fun i j => raw36895 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36895step0 raw36895; decide +kernel
      have hl : raw36895step0Labels = raw36895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36895 raw36895Labels permutation346 hz
    mixedMoment B raw36895step0 raw36895step0Labels = mixedMoment B raw36895step1 raw36895step1Labels := by
      have ha : raw36895step1 = (fun i j => raw36895step0 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36895step1 raw36895step0; decide +kernel
      have hl : raw36895step1Labels = raw36895step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36895step0 raw36895step0Labels permutation56 permutation6
    mixedMoment B raw36895step1 raw36895step1Labels = mixedMoment B raw36895step2 raw36895step2Labels := by
      have ha : raw36895step2 = raw36895step1 := by apply Matrix.ext; unfold raw36895step2 raw36895step1; decide +kernel
      have hl : raw36895step1Labels = labelEmbedding9 ∘ raw36895step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36895step1 raw36895step1Labels raw36895step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw36896 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36896step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36896step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36896step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36896step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36896step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36896step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36896 raw36896Labels = mixedMoment B node5314 node5314Labels := by
  calc
    mixedMoment B raw36896 raw36896Labels = mixedMoment B raw36896step0 raw36896step0Labels := by
      have ha : raw36896step0 = (fun i j => raw36896 (permutation154 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36896step0 raw36896; decide +kernel
      have hl : raw36896step0Labels = raw36896Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36896 raw36896Labels permutation154 permutation4
    mixedMoment B raw36896step0 raw36896step0Labels = mixedMoment B raw36896step1 raw36896step1Labels := by
      have ha : raw36896step1 = -raw36896step0 := by apply Matrix.ext; change ∀ i j, raw36896step1 i j = -(raw36896step0 i j); unfold raw36896step1 raw36896step0; decide +kernel
      have hl : raw36896step1Labels = raw36896step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36896step1 raw36896step1Labels = mixedMoment B raw36896step2 raw36896step2Labels := by
      have ha : raw36896step2 = raw36896step1 := by apply Matrix.ext; unfold raw36896step2 raw36896step1; decide +kernel
      have hl : raw36896step1Labels = labelEmbedding7 ∘ raw36896step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36896step1 raw36896step1Labels raw36896step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5314 node5314Labels := by rfl

def raw36897 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36897step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36897step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36897step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36897step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36897step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36897step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36897 raw36897Labels = mixedMoment B node4987 node4987Labels := by
  calc
    mixedMoment B raw36897 raw36897Labels = mixedMoment B raw36897step0 raw36897step0Labels := by
      have ha : raw36897step0 = (fun i j => raw36897 (permutation267 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36897step0 raw36897; decide +kernel
      have hl : raw36897step0Labels = raw36897Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36897 raw36897Labels permutation267 permutation4
    mixedMoment B raw36897step0 raw36897step0Labels = mixedMoment B raw36897step1 raw36897step1Labels := by
      have ha : raw36897step1 = -raw36897step0 := by apply Matrix.ext; change ∀ i j, raw36897step1 i j = -(raw36897step0 i j); unfold raw36897step1 raw36897step0; decide +kernel
      have hl : raw36897step1Labels = raw36897step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36897step1 raw36897step1Labels = mixedMoment B raw36897step2 raw36897step2Labels := by
      have ha : raw36897step2 = raw36897step1 := by apply Matrix.ext; unfold raw36897step2 raw36897step1; decide +kernel
      have hl : raw36897step1Labels = labelEmbedding7 ∘ raw36897step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36897step1 raw36897step1Labels raw36897step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4987 node4987Labels := by rfl

def raw36898 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36898step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw36898step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36898step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw36898step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36898 raw36898Labels = mixedMoment B node5333 node5333Labels := by
  calc
    mixedMoment B raw36898 raw36898Labels = mixedMoment B raw36898step0 raw36898step0Labels := by
      have ha : raw36898step0 = (fun i j => raw36898 (permutation660 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36898step0 raw36898; decide +kernel
      have hl : raw36898step0Labels = raw36898Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36898 raw36898Labels permutation660 permutation4
    mixedMoment B raw36898step0 raw36898step0Labels = mixedMoment B raw36898step1 raw36898step1Labels := by
      have ha : raw36898step1 = raw36898step0 := by apply Matrix.ext; unfold raw36898step1 raw36898step0; decide +kernel
      have hl : raw36898step0Labels = labelEmbedding7 ∘ raw36898step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36898step0 raw36898step0Labels raw36898step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5333 node5333Labels := by rfl

def raw36899 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw36899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36899step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36899step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36899step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36899 raw36899Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw36899 raw36899Labels = mixedMoment B raw36899step0 raw36899step0Labels := by
      have ha : raw36899step0 = (fun i j => raw36899 (permutation267 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36899step0 raw36899; decide +kernel
      have hl : raw36899step0Labels = raw36899Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36899 raw36899Labels permutation267 permutation6
    mixedMoment B raw36899step0 raw36899step0Labels = mixedMoment B raw36899step1 raw36899step1Labels := by
      have ha : raw36899step1 = raw36899step0 := by apply Matrix.ext; unfold raw36899step1 raw36899step0; decide +kernel
      have hl : raw36899step0Labels = labelEmbedding9 ∘ raw36899step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36899step0 raw36899step0Labels raw36899step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

def raw36900 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw36900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36900step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36900step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36900step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36900step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36900step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36900step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36900 raw36900Labels = mixedMoment B node5314 node5314Labels := by
  calc
    mixedMoment B raw36900 raw36900Labels = mixedMoment B raw36900step0 raw36900step0Labels := by
      have ha : raw36900step0 = (fun i j => raw36900 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36900step0 raw36900; decide +kernel
      have hl : raw36900step0Labels = raw36900Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36900 raw36900Labels permutation152 permutation4
    mixedMoment B raw36900step0 raw36900step0Labels = mixedMoment B raw36900step1 raw36900step1Labels := by
      have ha : raw36900step1 = -raw36900step0 := by apply Matrix.ext; change ∀ i j, raw36900step1 i j = -(raw36900step0 i j); unfold raw36900step1 raw36900step0; decide +kernel
      have hl : raw36900step1Labels = raw36900step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36900step1 raw36900step1Labels = mixedMoment B raw36900step2 raw36900step2Labels := by
      have ha : raw36900step2 = raw36900step1 := by apply Matrix.ext; unfold raw36900step2 raw36900step1; decide +kernel
      have hl : raw36900step1Labels = labelEmbedding7 ∘ raw36900step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36900step1 raw36900step1Labels raw36900step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5314 node5314Labels := by rfl

def raw36901 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw36901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36901step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw36901step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36901step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36901step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36901step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36901step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36901 raw36901Labels = mixedMoment B node4987 node4987Labels := by
  calc
    mixedMoment B raw36901 raw36901Labels = mixedMoment B raw36901step0 raw36901step0Labels := by
      have ha : raw36901step0 = (fun i j => raw36901 (permutation265 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36901step0 raw36901; decide +kernel
      have hl : raw36901step0Labels = raw36901Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36901 raw36901Labels permutation265 permutation4
    mixedMoment B raw36901step0 raw36901step0Labels = mixedMoment B raw36901step1 raw36901step1Labels := by
      have ha : raw36901step1 = -raw36901step0 := by apply Matrix.ext; change ∀ i j, raw36901step1 i j = -(raw36901step0 i j); unfold raw36901step1 raw36901step0; decide +kernel
      have hl : raw36901step1Labels = raw36901step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36901step1 raw36901step1Labels = mixedMoment B raw36901step2 raw36901step2Labels := by
      have ha : raw36901step2 = raw36901step1 := by apply Matrix.ext; unfold raw36901step2 raw36901step1; decide +kernel
      have hl : raw36901step1Labels = labelEmbedding7 ∘ raw36901step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36901step1 raw36901step1Labels raw36901step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4987 node4987Labels := by rfl

def raw36902 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw36902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36902step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw36902step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36902step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw36902step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36902 raw36902Labels = mixedMoment B node5333 node5333Labels := by
  calc
    mixedMoment B raw36902 raw36902Labels = mixedMoment B raw36902step0 raw36902step0Labels := by
      have ha : raw36902step0 = (fun i j => raw36902 (permutation684 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36902step0 raw36902; decide +kernel
      have hl : raw36902step0Labels = raw36902Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36902 raw36902Labels permutation684 permutation4
    mixedMoment B raw36902step0 raw36902step0Labels = mixedMoment B raw36902step1 raw36902step1Labels := by
      have ha : raw36902step1 = raw36902step0 := by apply Matrix.ext; unfold raw36902step1 raw36902step0; decide +kernel
      have hl : raw36902step0Labels = labelEmbedding7 ∘ raw36902step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36902step0 raw36902step0Labels raw36902step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5333 node5333Labels := by rfl

def raw36903 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -2, 2]]
def raw36903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36903step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36903step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36903step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36903step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36903 raw36903Labels = mixedMoment B node5344 node5344Labels := by
  calc
    mixedMoment B raw36903 raw36903Labels = mixedMoment B raw36903step0 raw36903step0Labels := by
      have ha : raw36903step0 = (fun i j => raw36903 (permutation687 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36903step0 raw36903; decide +kernel
      have hl : raw36903step0Labels = raw36903Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36903 raw36903Labels permutation687 permutation4
    mixedMoment B raw36903step0 raw36903step0Labels = mixedMoment B raw36903step1 raw36903step1Labels := by
      have ha : raw36903step1 = raw36903step0 := by apply Matrix.ext; unfold raw36903step1 raw36903step0; decide +kernel
      have hl : raw36903step0Labels = labelEmbedding7 ∘ raw36903step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36903step0 raw36903step0Labels raw36903step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5344 node5344Labels := by rfl

def raw36904 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw36904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36904step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36904step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36904step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36904 raw36904Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw36904 raw36904Labels = mixedMoment B raw36904step0 raw36904step0Labels := by
      have ha : raw36904step0 = (fun i j => raw36904 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36904step0 raw36904; decide +kernel
      have hl : raw36904step0Labels = raw36904Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36904 raw36904Labels permutation265 permutation6
    mixedMoment B raw36904step0 raw36904step0Labels = mixedMoment B raw36904step1 raw36904step1Labels := by
      have ha : raw36904step1 = raw36904step0 := by apply Matrix.ext; unfold raw36904step1 raw36904step0; decide +kernel
      have hl : raw36904step0Labels = labelEmbedding9 ∘ raw36904step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36904step0 raw36904step0Labels raw36904step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

def raw36905 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw36905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw36905step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw36905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36905 raw36905Labels = mixedMoment B node5025 node5025Labels := by
  calc
    mixedMoment B raw36905 raw36905Labels = mixedMoment B raw36905step0 raw36905step0Labels := by
      have ha : raw36905step0 = (fun i j => raw36905 (permutation663 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36905step0 raw36905; decide +kernel
      have hl : raw36905step0Labels = raw36905Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36905 raw36905Labels permutation663 permutation4
    mixedMoment B raw36905step0 raw36905step0Labels = mixedMoment B raw36905step1 raw36905step1Labels := by
      have ha : raw36905step1 = raw36905step0 := by apply Matrix.ext; unfold raw36905step1 raw36905step0; decide +kernel
      have hl : raw36905step0Labels = labelEmbedding7 ∘ raw36905step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36905step0 raw36905step0Labels raw36905step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5025 node5025Labels := by rfl

def raw36906 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 3, -2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw36906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36906step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw36906step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36906step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw36906step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36906step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw36906step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36906 raw36906Labels = mixedMoment B node4986 node4986Labels := by
  calc
    mixedMoment B raw36906 raw36906Labels = mixedMoment B raw36906step0 raw36906step0Labels := by
      have ha : raw36906step0 = (fun i j => raw36906 (permutation265 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36906step0 raw36906; decide +kernel
      have hl : raw36906step0Labels = raw36906Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36906 raw36906Labels permutation265 permutation4
    mixedMoment B raw36906step0 raw36906step0Labels = mixedMoment B raw36906step1 raw36906step1Labels := by
      have ha : raw36906step1 = -raw36906step0 := by apply Matrix.ext; change ∀ i j, raw36906step1 i j = -(raw36906step0 i j); unfold raw36906step1 raw36906step0; decide +kernel
      have hl : raw36906step1Labels = raw36906step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36906step1 raw36906step1Labels = mixedMoment B raw36906step2 raw36906step2Labels := by
      have ha : raw36906step2 = raw36906step1 := by apply Matrix.ext; unfold raw36906step2 raw36906step1; decide +kernel
      have hl : raw36906step1Labels = labelEmbedding7 ∘ raw36906step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36906step1 raw36906step1Labels raw36906step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4986 node4986Labels := by rfl

def raw36907 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw36907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw36907step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36907step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw36907step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36907 raw36907Labels = mixedMoment B node5030 node5030Labels := by
  calc
    mixedMoment B raw36907 raw36907Labels = mixedMoment B raw36907step0 raw36907step0Labels := by
      have ha : raw36907step0 = (fun i j => raw36907 (permutation660 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36907step0 raw36907; decide +kernel
      have hl : raw36907step0Labels = raw36907Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36907 raw36907Labels permutation660 permutation4
    mixedMoment B raw36907step0 raw36907step0Labels = mixedMoment B raw36907step1 raw36907step1Labels := by
      have ha : raw36907step1 = raw36907step0 := by apply Matrix.ext; unfold raw36907step1 raw36907step0; decide +kernel
      have hl : raw36907step0Labels = labelEmbedding7 ∘ raw36907step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36907step0 raw36907step0Labels raw36907step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5030 node5030Labels := by rfl

def raw36908 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw36908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36908step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36908step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36908step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36908 raw36908Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw36908 raw36908Labels = mixedMoment B raw36908step0 raw36908step0Labels := by
      have ha : raw36908step0 = (fun i j => raw36908 (permutation687 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36908step0 raw36908; decide +kernel
      have hl : raw36908step0Labels = raw36908Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36908 raw36908Labels permutation687 permutation4
    mixedMoment B raw36908step0 raw36908step0Labels = mixedMoment B raw36908step1 raw36908step1Labels := by
      have ha : raw36908step1 = raw36908step0 := by apply Matrix.ext; unfold raw36908step1 raw36908step0; decide +kernel
      have hl : raw36908step0Labels = labelEmbedding7 ∘ raw36908step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36908step0 raw36908step0Labels raw36908step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

def raw36909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36909step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36909 raw36909Labels = mixedMoment B node4998 node4998Labels := by
  calc
    mixedMoment B raw36909 raw36909Labels = mixedMoment B raw36909step0 raw36909step0Labels := by
      have ha : raw36909step0 = (fun i j => raw36909 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36909step0 raw36909; decide +kernel
      have hl : raw36909step0Labels = raw36909Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36909 raw36909Labels permutation265 permutation2
    _ = mixedMoment B node4998 node4998Labels := by rfl

def raw36910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36910Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36910step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36910step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36910step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36910step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36910step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36910 raw36910Labels = mixedMoment B node5363 node5363Labels := by
  calc
    mixedMoment B raw36910 raw36910Labels = mixedMoment B raw36910step0 raw36910step0Labels := by
      have ha : raw36910step0 = (fun i j => raw36910 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36910step0 raw36910; decide +kernel
      have hl : raw36910step0Labels = raw36910Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36910 raw36910Labels permutation265 permutation7
    mixedMoment B raw36910step0 raw36910step0Labels = mixedMoment B raw36910step1 raw36910step1Labels := by
      have ha : raw36910step1 = -raw36910step0 := by apply Matrix.ext; change ∀ i j, raw36910step1 i j = -(raw36910step0 i j); unfold raw36910step1 raw36910step0; decide +kernel
      have hl : raw36910step1Labels = raw36910step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36910step1 raw36910step1Labels = mixedMoment B raw36910step2 raw36910step2Labels := by
      have ha : raw36910step2 = raw36910step1 := by apply Matrix.ext; unfold raw36910step2 raw36910step1; decide +kernel
      have hl : raw36910step1Labels = labelEmbedding10 ∘ raw36910step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36910step1 raw36910step1Labels raw36910step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5363 node5363Labels := by rfl

def raw36911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw36911step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36911step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36911step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36911step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36911step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36911 raw36911Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw36911 raw36911Labels = mixedMoment B raw36911step0 raw36911step0Labels := by
      have ha : raw36911step0 = (fun i j => raw36911 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36911step0 raw36911; decide +kernel
      have hl : raw36911step0Labels = raw36911Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36911 raw36911Labels permutation265 permutation7
    mixedMoment B raw36911step0 raw36911step0Labels = mixedMoment B raw36911step1 raw36911step1Labels := by
      have ha : raw36911step1 = -raw36911step0 := by apply Matrix.ext; change ∀ i j, raw36911step1 i j = -(raw36911step0 i j); unfold raw36911step1 raw36911step0; decide +kernel
      have hl : raw36911step1Labels = raw36911step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36911step1 raw36911step1Labels = mixedMoment B raw36911step2 raw36911step2Labels := by
      have ha : raw36911step2 = raw36911step1 := by apply Matrix.ext; unfold raw36911step2 raw36911step1; decide +kernel
      have hl : raw36911step1Labels = labelEmbedding10 ∘ raw36911step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36911step1 raw36911step1Labels raw36911step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5365 node5365Labels := by rfl

def raw36912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw36912Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw36912step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36912step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36912step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36912step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36912step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36912 raw36912Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw36912 raw36912Labels = mixedMoment B raw36912step0 raw36912step0Labels := by
      have ha : raw36912step0 = (fun i j => raw36912 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36912step0 raw36912; decide +kernel
      have hl : raw36912step0Labels = raw36912Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36912 raw36912Labels permutation267 permutation7
    mixedMoment B raw36912step0 raw36912step0Labels = mixedMoment B raw36912step1 raw36912step1Labels := by
      have ha : raw36912step1 = -raw36912step0 := by apply Matrix.ext; change ∀ i j, raw36912step1 i j = -(raw36912step0 i j); unfold raw36912step1 raw36912step0; decide +kernel
      have hl : raw36912step1Labels = raw36912step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36912step1 raw36912step1Labels = mixedMoment B raw36912step2 raw36912step2Labels := by
      have ha : raw36912step2 = raw36912step1 := by apply Matrix.ext; unfold raw36912step2 raw36912step1; decide +kernel
      have hl : raw36912step1Labels = labelEmbedding10 ∘ raw36912step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36912step1 raw36912step1Labels raw36912step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5365 node5365Labels := by rfl

def raw36913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw36913step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36913step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36913step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36913step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36913 raw36913Labels = mixedMoment B node5366 node5366Labels := by
  calc
    mixedMoment B raw36913 raw36913Labels = mixedMoment B raw36913step0 raw36913step0Labels := by
      have ha : raw36913step0 = (fun i j => raw36913 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36913step0 raw36913; decide +kernel
      have hl : raw36913step0Labels = raw36913Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36913 raw36913Labels permutation265 permutation7
    mixedMoment B raw36913step0 raw36913step0Labels = mixedMoment B raw36913step1 raw36913step1Labels := by
      have ha : raw36913step1 = -raw36913step0 := by apply Matrix.ext; change ∀ i j, raw36913step1 i j = -(raw36913step0 i j); unfold raw36913step1 raw36913step0; decide +kernel
      have hl : raw36913step1Labels = raw36913step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36913step1 raw36913step1Labels = mixedMoment B raw36913step2 raw36913step2Labels := by
      have ha : raw36913step2 = raw36913step1 := by apply Matrix.ext; unfold raw36913step2 raw36913step1; decide +kernel
      have hl : raw36913step1Labels = labelEmbedding10 ∘ raw36913step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36913step1 raw36913step1Labels raw36913step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5366 node5366Labels := by rfl

def raw36914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36914 raw36914Labels = mixedMoment B node4998 node4998Labels := by
  calc
    _ = mixedMoment B node4998 node4998Labels := by rfl

def raw36915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36915Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36915step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36915step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36915step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36915step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36915step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36915 raw36915Labels = mixedMoment B node5363 node5363Labels := by
  calc
    mixedMoment B raw36915 raw36915Labels = mixedMoment B raw36915step0 raw36915step0Labels := by
      have ha : raw36915step0 = (fun i j => raw36915 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36915step0 raw36915; decide +kernel
      have hl : raw36915step0Labels = raw36915Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36915 raw36915Labels permutation152 permutation7
    mixedMoment B raw36915step0 raw36915step0Labels = mixedMoment B raw36915step1 raw36915step1Labels := by
      have ha : raw36915step1 = -raw36915step0 := by apply Matrix.ext; change ∀ i j, raw36915step1 i j = -(raw36915step0 i j); unfold raw36915step1 raw36915step0; decide +kernel
      have hl : raw36915step1Labels = raw36915step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36915step1 raw36915step1Labels = mixedMoment B raw36915step2 raw36915step2Labels := by
      have ha : raw36915step2 = raw36915step1 := by apply Matrix.ext; unfold raw36915step2 raw36915step1; decide +kernel
      have hl : raw36915step1Labels = labelEmbedding10 ∘ raw36915step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36915step1 raw36915step1Labels raw36915step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5363 node5363Labels := by rfl

def raw36916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36916Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36916step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw36916step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36916step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36916step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36916step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36916step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36916 raw36916Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw36916 raw36916Labels = mixedMoment B raw36916step0 raw36916step0Labels := by
      have ha : raw36916step0 = (fun i j => raw36916 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36916step0 raw36916; decide +kernel
      have hl : raw36916step0Labels = raw36916Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36916 raw36916Labels permutation152 permutation7
    mixedMoment B raw36916step0 raw36916step0Labels = mixedMoment B raw36916step1 raw36916step1Labels := by
      have ha : raw36916step1 = -raw36916step0 := by apply Matrix.ext; change ∀ i j, raw36916step1 i j = -(raw36916step0 i j); unfold raw36916step1 raw36916step0; decide +kernel
      have hl : raw36916step1Labels = raw36916step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36916step1 raw36916step1Labels = mixedMoment B raw36916step2 raw36916step2Labels := by
      have ha : raw36916step2 = raw36916step1 := by apply Matrix.ext; unfold raw36916step2 raw36916step1; decide +kernel
      have hl : raw36916step1Labels = labelEmbedding10 ∘ raw36916step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36916step1 raw36916step1Labels raw36916step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5365 node5365Labels := by rfl

def raw36917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw36917Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw36917step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36917step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36917step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36917step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36917step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36917 raw36917Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw36917 raw36917Labels = mixedMoment B raw36917step0 raw36917step0Labels := by
      have ha : raw36917step0 = (fun i j => raw36917 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36917step0 raw36917; decide +kernel
      have hl : raw36917step0Labels = raw36917Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36917 raw36917Labels permutation154 permutation7
    mixedMoment B raw36917step0 raw36917step0Labels = mixedMoment B raw36917step1 raw36917step1Labels := by
      have ha : raw36917step1 = -raw36917step0 := by apply Matrix.ext; change ∀ i j, raw36917step1 i j = -(raw36917step0 i j); unfold raw36917step1 raw36917step0; decide +kernel
      have hl : raw36917step1Labels = raw36917step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36917step1 raw36917step1Labels = mixedMoment B raw36917step2 raw36917step2Labels := by
      have ha : raw36917step2 = raw36917step1 := by apply Matrix.ext; unfold raw36917step2 raw36917step1; decide +kernel
      have hl : raw36917step1Labels = labelEmbedding10 ∘ raw36917step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36917step1 raw36917step1Labels raw36917step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5365 node5365Labels := by rfl

def raw36918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36918Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw36918step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36918step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36918step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36918step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36918step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36918 raw36918Labels = mixedMoment B node5366 node5366Labels := by
  calc
    mixedMoment B raw36918 raw36918Labels = mixedMoment B raw36918step0 raw36918step0Labels := by
      have ha : raw36918step0 = (fun i j => raw36918 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36918step0 raw36918; decide +kernel
      have hl : raw36918step0Labels = raw36918Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36918 raw36918Labels permutation152 permutation7
    mixedMoment B raw36918step0 raw36918step0Labels = mixedMoment B raw36918step1 raw36918step1Labels := by
      have ha : raw36918step1 = -raw36918step0 := by apply Matrix.ext; change ∀ i j, raw36918step1 i j = -(raw36918step0 i j); unfold raw36918step1 raw36918step0; decide +kernel
      have hl : raw36918step1Labels = raw36918step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36918step1 raw36918step1Labels = mixedMoment B raw36918step2 raw36918step2Labels := by
      have ha : raw36918step2 = raw36918step1 := by apply Matrix.ext; unfold raw36918step2 raw36918step1; decide +kernel
      have hl : raw36918step1Labels = labelEmbedding10 ∘ raw36918step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36918step1 raw36918step1Labels raw36918step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5366 node5366Labels := by rfl

def raw36919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36919Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36919 raw36919Labels = mixedMoment B node4916 node4916Labels := by
  calc
    _ = mixedMoment B node4916 node4916Labels := by rfl

def raw36920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36920Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36920step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36920 raw36920Labels = mixedMoment B node4916 node4916Labels := by
  calc
    mixedMoment B raw36920 raw36920Labels = mixedMoment B raw36920step0 raw36920step0Labels := by
      have ha : raw36920step0 = (fun i j => raw36920 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36920step0 raw36920; decide +kernel
      have hl : raw36920step0Labels = raw36920Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36920 raw36920Labels permutation265 permutation2
    _ = mixedMoment B node4916 node4916Labels := by rfl

def raw36921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36921Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36921step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36921step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36921 raw36921Labels = mixedMoment B node5325 node5325Labels := by
  calc
    mixedMoment B raw36921 raw36921Labels = mixedMoment B raw36921step0 raw36921step0Labels := by
      have ha : raw36921step0 = (fun i j => raw36921 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36921step0 raw36921; decide +kernel
      have hl : raw36921step0Labels = raw36921Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36921 raw36921Labels permutation158 permutation2
    _ = mixedMoment B node5325 node5325Labels := by rfl

def raw36922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw36922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36922step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36922 raw36922Labels = mixedMoment B node5325 node5325Labels := by
  calc
    mixedMoment B raw36922 raw36922Labels = mixedMoment B raw36922step0 raw36922step0Labels := by
      have ha : raw36922step0 = (fun i j => raw36922 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36922step0 raw36922; decide +kernel
      have hl : raw36922step0Labels = raw36922Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36922 raw36922Labels permutation164 permutation2
    _ = mixedMoment B node5325 node5325Labels := by rfl

def raw36923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36923step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw36923step0Labels : Fin 2 → Fin 3 := ![0, 2]

def raw36923step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw36923step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical36923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36923 raw36923Labels = mixedMoment B node4087 node4087Labels := by
  calc
    mixedMoment B raw36923 raw36923Labels = mixedMoment B raw36923step0 raw36923step0Labels := by
      have hz : ∀ i, raw36923 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw36923step0 = (fun i j => raw36923 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw36923step0 raw36923; decide +kernel
      have hl : raw36923step0Labels = (fun j => raw36923Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw36923 raw36923Labels permutation4 hz
    mixedMoment B raw36923step0 raw36923step0Labels = mixedMoment B raw36923step1 raw36923step1Labels := by
      have ha : raw36923step1 = raw36923step0 := by apply Matrix.ext; unfold raw36923step1 raw36923step0; decide +kernel
      have hl : raw36923step0Labels = labelEmbedding2 ∘ raw36923step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36923step0 raw36923step0Labels raw36923step1Labels labelEmbedding2 hl
    _ = mixedMoment B node4087 node4087Labels := by rfl

def raw36924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36924step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36924 raw36924Labels = mixedMoment B node4906 node4906Labels := by
  calc
    mixedMoment B raw36924 raw36924Labels = mixedMoment B raw36924step0 raw36924step0Labels := by
      have ha : raw36924step0 = (fun i j => raw36924 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36924step0 raw36924; decide +kernel
      have hl : raw36924step0Labels = raw36924Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36924 raw36924Labels permutation154 permutation2
    _ = mixedMoment B node4906 node4906Labels := by rfl

def raw36925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36925step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36925 raw36925Labels = mixedMoment B node4906 node4906Labels := by
  calc
    mixedMoment B raw36925 raw36925Labels = mixedMoment B raw36925step0 raw36925step0Labels := by
      have ha : raw36925step0 = (fun i j => raw36925 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36925step0 raw36925; decide +kernel
      have hl : raw36925step0Labels = raw36925Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36925 raw36925Labels permutation267 permutation2
    _ = mixedMoment B node4906 node4906Labels := by rfl

def raw36926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36926step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36926step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36926 raw36926Labels = mixedMoment B node5319 node5319Labels := by
  calc
    mixedMoment B raw36926 raw36926Labels = mixedMoment B raw36926step0 raw36926step0Labels := by
      have ha : raw36926step0 = (fun i j => raw36926 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36926step0 raw36926; decide +kernel
      have hl : raw36926step0Labels = raw36926Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36926 raw36926Labels permutation154 permutation2
    _ = mixedMoment B node5319 node5319Labels := by rfl

def raw36927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw36927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36927 raw36927Labels = mixedMoment B node5321 node5321Labels := by
  calc
    mixedMoment B raw36927 raw36927Labels = mixedMoment B raw36927step0 raw36927step0Labels := by
      have ha : raw36927step0 = (fun i j => raw36927 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36927step0 raw36927; decide +kernel
      have hl : raw36927step0Labels = raw36927Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36927 raw36927Labels permutation154 permutation2
    _ = mixedMoment B node5321 node5321Labels := by rfl

def raw36928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36928 raw36928Labels = mixedMoment B node5325 node5325Labels := by
  calc
    mixedMoment B raw36928 raw36928Labels = mixedMoment B raw36928step0 raw36928step0Labels := by
      have ha : raw36928step0 = (fun i j => raw36928 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36928step0 raw36928; decide +kernel
      have hl : raw36928step0Labels = raw36928Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36928 raw36928Labels permutation155 permutation2
    _ = mixedMoment B node5325 node5325Labels := by rfl

def raw36929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36929 raw36929Labels = mixedMoment B node4906 node4906Labels := by
  calc
    _ = mixedMoment B node4906 node4906Labels := by rfl

def raw36930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36930 raw36930Labels = mixedMoment B node4906 node4906Labels := by
  calc
    mixedMoment B raw36930 raw36930Labels = mixedMoment B raw36930step0 raw36930step0Labels := by
      have ha : raw36930step0 = (fun i j => raw36930 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36930step0 raw36930; decide +kernel
      have hl : raw36930step0Labels = raw36930Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36930 raw36930Labels permutation265 permutation2
    _ = mixedMoment B node4906 node4906Labels := by rfl

def raw36931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36931 raw36931Labels = mixedMoment B node5319 node5319Labels := by
  calc
    _ = mixedMoment B node5319 node5319Labels := by rfl

def raw36932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36932 raw36932Labels = mixedMoment B node5321 node5321Labels := by
  calc
    _ = mixedMoment B node5321 node5321Labels := by rfl

def raw36933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw36933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36933step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36933 raw36933Labels = mixedMoment B node5325 node5325Labels := by
  calc
    mixedMoment B raw36933 raw36933Labels = mixedMoment B raw36933step0 raw36933step0Labels := by
      have ha : raw36933step0 = (fun i j => raw36933 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36933step0 raw36933; decide +kernel
      have hl : raw36933step0Labels = raw36933Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36933 raw36933Labels permutation153 permutation2
    _ = mixedMoment B node5325 node5325Labels := by rfl

def raw36934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36934 raw36934Labels = mixedMoment B node4904 node4904Labels := by
  calc
    _ = mixedMoment B node4904 node4904Labels := by rfl

def raw36935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36935 raw36935Labels = mixedMoment B node4904 node4904Labels := by
  calc
    mixedMoment B raw36935 raw36935Labels = mixedMoment B raw36935step0 raw36935step0Labels := by
      have ha : raw36935step0 = (fun i j => raw36935 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36935step0 raw36935; decide +kernel
      have hl : raw36935step0Labels = raw36935Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36935 raw36935Labels permutation265 permutation2
    _ = mixedMoment B node4904 node4904Labels := by rfl

def raw36936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36936step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 2, 0]]
def raw36936step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36936step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -2, 0]]
def raw36936step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36936step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -2, 0]]
def raw36936step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36936 raw36936Labels = mixedMoment B node5118 node5118Labels := by
  calc
    mixedMoment B raw36936 raw36936Labels = mixedMoment B raw36936step0 raw36936step0Labels := by
      have ha : raw36936step0 = (fun i j => raw36936 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36936step0 raw36936; decide +kernel
      have hl : raw36936step0Labels = raw36936Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36936 raw36936Labels permutation663 permutation3
    mixedMoment B raw36936step0 raw36936step0Labels = mixedMoment B raw36936step1 raw36936step1Labels := by
      have ha : raw36936step1 = -raw36936step0 := by apply Matrix.ext; change ∀ i j, raw36936step1 i j = -(raw36936step0 i j); unfold raw36936step1 raw36936step0; decide +kernel
      have hl : raw36936step1Labels = raw36936step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36936step1 raw36936step1Labels = mixedMoment B raw36936step2 raw36936step2Labels := by
      have ha : raw36936step2 = raw36936step1 := by apply Matrix.ext; unfold raw36936step2 raw36936step1; decide +kernel
      have hl : raw36936step1Labels = labelEmbedding6 ∘ raw36936step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36936step1 raw36936step1Labels raw36936step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5118 node5118Labels := by rfl

def raw36937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36937step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 2, 0]]
def raw36937step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36937step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw36937step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36937step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw36937step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36937 raw36937Labels = mixedMoment B node5142 node5142Labels := by
  calc
    mixedMoment B raw36937 raw36937Labels = mixedMoment B raw36937step0 raw36937step0Labels := by
      have ha : raw36937step0 = (fun i j => raw36937 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36937step0 raw36937; decide +kernel
      have hl : raw36937step0Labels = raw36937Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36937 raw36937Labels permutation681 permutation3
    mixedMoment B raw36937step0 raw36937step0Labels = mixedMoment B raw36937step1 raw36937step1Labels := by
      have ha : raw36937step1 = -raw36937step0 := by apply Matrix.ext; change ∀ i j, raw36937step1 i j = -(raw36937step0 i j); unfold raw36937step1 raw36937step0; decide +kernel
      have hl : raw36937step1Labels = raw36937step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36937step1 raw36937step1Labels = mixedMoment B raw36937step2 raw36937step2Labels := by
      have ha : raw36937step2 = raw36937step1 := by apply Matrix.ext; unfold raw36937step2 raw36937step1; decide +kernel
      have hl : raw36937step1Labels = labelEmbedding6 ∘ raw36937step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36937step1 raw36937step1Labels raw36937step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5142 node5142Labels := by rfl

def raw36938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw36938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36938step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 2, 0]]
def raw36938step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36938step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw36938step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36938step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw36938step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36938 raw36938Labels = mixedMoment B node5142 node5142Labels := by
  calc
    mixedMoment B raw36938 raw36938Labels = mixedMoment B raw36938step0 raw36938step0Labels := by
      have ha : raw36938step0 = (fun i j => raw36938 (permutation657 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36938step0 raw36938; decide +kernel
      have hl : raw36938step0Labels = raw36938Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36938 raw36938Labels permutation657 permutation3
    mixedMoment B raw36938step0 raw36938step0Labels = mixedMoment B raw36938step1 raw36938step1Labels := by
      have ha : raw36938step1 = -raw36938step0 := by apply Matrix.ext; change ∀ i j, raw36938step1 i j = -(raw36938step0 i j); unfold raw36938step1 raw36938step0; decide +kernel
      have hl : raw36938step1Labels = raw36938step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36938step1 raw36938step1Labels = mixedMoment B raw36938step2 raw36938step2Labels := by
      have ha : raw36938step2 = raw36938step1 := by apply Matrix.ext; unfold raw36938step2 raw36938step1; decide +kernel
      have hl : raw36938step1Labels = labelEmbedding6 ∘ raw36938step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36938step1 raw36938step1Labels raw36938step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5142 node5142Labels := by rfl

def raw36939 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36939step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36939step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36939step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36939 raw36939Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw36939 raw36939Labels = mixedMoment B raw36939step0 raw36939step0Labels := by
      have ha : raw36939step0 = (fun i j => raw36939 (permutation267 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36939step0 raw36939; decide +kernel
      have hl : raw36939step0Labels = raw36939Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36939 raw36939Labels permutation267 permutation6
    mixedMoment B raw36939step0 raw36939step0Labels = mixedMoment B raw36939step1 raw36939step1Labels := by
      have ha : raw36939step1 = raw36939step0 := by apply Matrix.ext; unfold raw36939step1 raw36939step0; decide +kernel
      have hl : raw36939step0Labels = labelEmbedding9 ∘ raw36939step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36939step0 raw36939step0Labels raw36939step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw36940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![1, 1, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw36940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36940step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36940step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36940step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36940step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36940step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36940step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36940 raw36940Labels = mixedMoment B node5013 node5013Labels := by
  calc
    mixedMoment B raw36940 raw36940Labels = mixedMoment B raw36940step0 raw36940step0Labels := by
      have ha : raw36940step0 = (fun i j => raw36940 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36940step0 raw36940; decide +kernel
      have hl : raw36940step0Labels = raw36940Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36940 raw36940Labels permutation152 permutation4
    mixedMoment B raw36940step0 raw36940step0Labels = mixedMoment B raw36940step1 raw36940step1Labels := by
      have ha : raw36940step1 = -raw36940step0 := by apply Matrix.ext; change ∀ i j, raw36940step1 i j = -(raw36940step0 i j); unfold raw36940step1 raw36940step0; decide +kernel
      have hl : raw36940step1Labels = raw36940step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36940step1 raw36940step1Labels = mixedMoment B raw36940step2 raw36940step2Labels := by
      have ha : raw36940step2 = raw36940step1 := by apply Matrix.ext; unfold raw36940step2 raw36940step1; decide +kernel
      have hl : raw36940step1Labels = labelEmbedding7 ∘ raw36940step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36940step1 raw36940step1Labels raw36940step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5013 node5013Labels := by rfl

def raw36941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![0, 2, -2], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw36941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw36941step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36941step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36941step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36941step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36941step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36941 raw36941Labels = mixedMoment B node4917 node4917Labels := by
  calc
    mixedMoment B raw36941 raw36941Labels = mixedMoment B raw36941step0 raw36941step0Labels := by
      have ha : raw36941step0 = (fun i j => raw36941 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36941step0 raw36941; decide +kernel
      have hl : raw36941step0Labels = raw36941Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36941 raw36941Labels permutation161 permutation4
    mixedMoment B raw36941step0 raw36941step0Labels = mixedMoment B raw36941step1 raw36941step1Labels := by
      have ha : raw36941step1 = -raw36941step0 := by apply Matrix.ext; change ∀ i j, raw36941step1 i j = -(raw36941step0 i j); unfold raw36941step1 raw36941step0; decide +kernel
      have hl : raw36941step1Labels = raw36941step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36941step1 raw36941step1Labels = mixedMoment B raw36941step2 raw36941step2Labels := by
      have ha : raw36941step2 = raw36941step1 := by apply Matrix.ext; unfold raw36941step2 raw36941step1; decide +kernel
      have hl : raw36941step1Labels = labelEmbedding7 ∘ raw36941step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36941step1 raw36941step1Labels raw36941step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4917 node4917Labels := by rfl

def raw36942 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 3, -2], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw36942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw36942step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36942step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36942step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36942step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36942step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36942 raw36942Labels = mixedMoment B node4917 node4917Labels := by
  calc
    mixedMoment B raw36942 raw36942Labels = mixedMoment B raw36942step0 raw36942step0Labels := by
      have ha : raw36942step0 = (fun i j => raw36942 (permutation274 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36942step0 raw36942; decide +kernel
      have hl : raw36942step0Labels = raw36942Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36942 raw36942Labels permutation274 permutation4
    mixedMoment B raw36942step0 raw36942step0Labels = mixedMoment B raw36942step1 raw36942step1Labels := by
      have ha : raw36942step1 = -raw36942step0 := by apply Matrix.ext; change ∀ i j, raw36942step1 i j = -(raw36942step0 i j); unfold raw36942step1 raw36942step0; decide +kernel
      have hl : raw36942step1Labels = raw36942step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36942step1 raw36942step1Labels = mixedMoment B raw36942step2 raw36942step2Labels := by
      have ha : raw36942step2 = raw36942step1 := by apply Matrix.ext; unfold raw36942step2 raw36942step1; decide +kernel
      have hl : raw36942step1Labels = labelEmbedding7 ∘ raw36942step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36942step1 raw36942step1Labels raw36942step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4917 node4917Labels := by rfl

def raw36943 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw36943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw36943step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36943step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36943step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36943step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36943step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36943 raw36943Labels = mixedMoment B node5326 node5326Labels := by
  calc
    mixedMoment B raw36943 raw36943Labels = mixedMoment B raw36943step0 raw36943step0Labels := by
      have ha : raw36943step0 = (fun i j => raw36943 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36943step0 raw36943; decide +kernel
      have hl : raw36943step0Labels = raw36943Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36943 raw36943Labels permutation161 permutation4
    mixedMoment B raw36943step0 raw36943step0Labels = mixedMoment B raw36943step1 raw36943step1Labels := by
      have ha : raw36943step1 = -raw36943step0 := by apply Matrix.ext; change ∀ i j, raw36943step1 i j = -(raw36943step0 i j); unfold raw36943step1 raw36943step0; decide +kernel
      have hl : raw36943step1Labels = raw36943step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36943step1 raw36943step1Labels = mixedMoment B raw36943step2 raw36943step2Labels := by
      have ha : raw36943step2 = raw36943step1 := by apply Matrix.ext; unfold raw36943step2 raw36943step1; decide +kernel
      have hl : raw36943step1Labels = labelEmbedding7 ∘ raw36943step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36943step1 raw36943step1Labels raw36943step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5326 node5326Labels := by rfl

def raw36944 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw36944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw36944step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36944step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36944step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36944step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36944step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36944 raw36944Labels = mixedMoment B node5328 node5328Labels := by
  calc
    mixedMoment B raw36944 raw36944Labels = mixedMoment B raw36944step0 raw36944step0Labels := by
      have ha : raw36944step0 = (fun i j => raw36944 (permutation173 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36944step0 raw36944; decide +kernel
      have hl : raw36944step0Labels = raw36944Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36944 raw36944Labels permutation173 permutation4
    mixedMoment B raw36944step0 raw36944step0Labels = mixedMoment B raw36944step1 raw36944step1Labels := by
      have ha : raw36944step1 = -raw36944step0 := by apply Matrix.ext; change ∀ i j, raw36944step1 i j = -(raw36944step0 i j); unfold raw36944step1 raw36944step0; decide +kernel
      have hl : raw36944step1Labels = raw36944step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36944step1 raw36944step1Labels = mixedMoment B raw36944step2 raw36944step2Labels := by
      have ha : raw36944step2 = raw36944step1 := by apply Matrix.ext; unfold raw36944step2 raw36944step1; decide +kernel
      have hl : raw36944step1Labels = labelEmbedding7 ∘ raw36944step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36944step1 raw36944step1Labels raw36944step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5328 node5328Labels := by rfl

def raw36945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw36945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36945step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36945step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36945step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36945step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36945step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36945 raw36945Labels = mixedMoment B node4912 node4912Labels := by
  calc
    mixedMoment B raw36945 raw36945Labels = mixedMoment B raw36945step0 raw36945step0Labels := by
      have ha : raw36945step0 = (fun i j => raw36945 (permutation155 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36945step0 raw36945; decide +kernel
      have hl : raw36945step0Labels = raw36945Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36945 raw36945Labels permutation155 permutation4
    mixedMoment B raw36945step0 raw36945step0Labels = mixedMoment B raw36945step1 raw36945step1Labels := by
      have ha : raw36945step1 = -raw36945step0 := by apply Matrix.ext; change ∀ i j, raw36945step1 i j = -(raw36945step0 i j); unfold raw36945step1 raw36945step0; decide +kernel
      have hl : raw36945step1Labels = raw36945step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36945step1 raw36945step1Labels = mixedMoment B raw36945step2 raw36945step2Labels := by
      have ha : raw36945step2 = raw36945step1 := by apply Matrix.ext; unfold raw36945step2 raw36945step1; decide +kernel
      have hl : raw36945step1Labels = labelEmbedding7 ∘ raw36945step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36945step1 raw36945step1Labels raw36945step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4912 node4912Labels := by rfl

def raw36946 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 3, -2], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw36946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36946step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36946step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36946step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36946step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36946step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36946step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36946 raw36946Labels = mixedMoment B node4912 node4912Labels := by
  calc
    mixedMoment B raw36946 raw36946Labels = mixedMoment B raw36946step0 raw36946step0Labels := by
      have ha : raw36946step0 = (fun i j => raw36946 (permutation268 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36946step0 raw36946; decide +kernel
      have hl : raw36946step0Labels = raw36946Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36946 raw36946Labels permutation268 permutation4
    mixedMoment B raw36946step0 raw36946step0Labels = mixedMoment B raw36946step1 raw36946step1Labels := by
      have ha : raw36946step1 = -raw36946step0 := by apply Matrix.ext; change ∀ i j, raw36946step1 i j = -(raw36946step0 i j); unfold raw36946step1 raw36946step0; decide +kernel
      have hl : raw36946step1Labels = raw36946step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36946step1 raw36946step1Labels = mixedMoment B raw36946step2 raw36946step2Labels := by
      have ha : raw36946step2 = raw36946step1 := by apply Matrix.ext; unfold raw36946step2 raw36946step1; decide +kernel
      have hl : raw36946step1Labels = labelEmbedding7 ∘ raw36946step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36946step1 raw36946step1Labels raw36946step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4912 node4912Labels := by rfl

def raw36947 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw36947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw36947step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36947step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36947step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36947step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36947step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36947step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36947step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36947 raw36947Labels = mixedMoment B node5331 node5331Labels := by
  calc
    mixedMoment B raw36947 raw36947Labels = mixedMoment B raw36947step0 raw36947step0Labels := by
      have hz : ∀ j, raw36947 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36947step0 = (fun i j => raw36947 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36947step0 raw36947; decide +kernel
      have hl : raw36947step0Labels = raw36947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36947 raw36947Labels permutation346 hz
    mixedMoment B raw36947step0 raw36947step0Labels = mixedMoment B raw36947step1 raw36947step1Labels := by
      have ha : raw36947step1 = (fun i j => raw36947step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36947step1 raw36947step0; decide +kernel
      have hl : raw36947step1Labels = raw36947step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36947step0 raw36947step0Labels permutation35 permutation4
    mixedMoment B raw36947step1 raw36947step1Labels = mixedMoment B raw36947step2 raw36947step2Labels := by
      have ha : raw36947step2 = -raw36947step1 := by apply Matrix.ext; change ∀ i j, raw36947step2 i j = -(raw36947step1 i j); unfold raw36947step2 raw36947step1; decide +kernel
      have hl : raw36947step2Labels = raw36947step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36947step2 raw36947step2Labels = mixedMoment B raw36947step3 raw36947step3Labels := by
      have ha : raw36947step3 = raw36947step2 := by apply Matrix.ext; unfold raw36947step3 raw36947step2; decide +kernel
      have hl : raw36947step2Labels = labelEmbedding7 ∘ raw36947step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36947step2 raw36947step2Labels raw36947step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5331 node5331Labels := by rfl

def raw36948 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw36948Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36948step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36948step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36948step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36948 raw36948Labels = mixedMoment B node5326 node5326Labels := by
  calc
    mixedMoment B raw36948 raw36948Labels = mixedMoment B raw36948step0 raw36948step0Labels := by
      have ha : raw36948step0 = (fun i j => raw36948 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36948step0 raw36948; decide +kernel
      have hl : raw36948step0Labels = raw36948Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36948 raw36948Labels permutation154 permutation6
    mixedMoment B raw36948step0 raw36948step0Labels = mixedMoment B raw36948step1 raw36948step1Labels := by
      have ha : raw36948step1 = raw36948step0 := by apply Matrix.ext; unfold raw36948step1 raw36948step0; decide +kernel
      have hl : raw36948step0Labels = labelEmbedding9 ∘ raw36948step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36948step0 raw36948step0Labels raw36948step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5326 node5326Labels := by rfl

def raw36949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw36949Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36949step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36949step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36949step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36949step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36949step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36949 raw36949Labels = mixedMoment B node4912 node4912Labels := by
  calc
    mixedMoment B raw36949 raw36949Labels = mixedMoment B raw36949step0 raw36949step0Labels := by
      have ha : raw36949step0 = (fun i j => raw36949 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36949step0 raw36949; decide +kernel
      have hl : raw36949step0Labels = raw36949Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36949 raw36949Labels permutation153 permutation4
    mixedMoment B raw36949step0 raw36949step0Labels = mixedMoment B raw36949step1 raw36949step1Labels := by
      have ha : raw36949step1 = -raw36949step0 := by apply Matrix.ext; change ∀ i j, raw36949step1 i j = -(raw36949step0 i j); unfold raw36949step1 raw36949step0; decide +kernel
      have hl : raw36949step1Labels = raw36949step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36949step1 raw36949step1Labels = mixedMoment B raw36949step2 raw36949step2Labels := by
      have ha : raw36949step2 = raw36949step1 := by apply Matrix.ext; unfold raw36949step2 raw36949step1; decide +kernel
      have hl : raw36949step1Labels = labelEmbedding7 ∘ raw36949step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36949step1 raw36949step1Labels raw36949step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4912 node4912Labels := by rfl

def raw36950 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 3, -2], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw36950Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36950step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36950step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36950step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36950step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36950step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36950 raw36950Labels = mixedMoment B node4912 node4912Labels := by
  calc
    mixedMoment B raw36950 raw36950Labels = mixedMoment B raw36950step0 raw36950step0Labels := by
      have ha : raw36950step0 = (fun i j => raw36950 (permutation266 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36950step0 raw36950; decide +kernel
      have hl : raw36950step0Labels = raw36950Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36950 raw36950Labels permutation266 permutation4
    mixedMoment B raw36950step0 raw36950step0Labels = mixedMoment B raw36950step1 raw36950step1Labels := by
      have ha : raw36950step1 = -raw36950step0 := by apply Matrix.ext; change ∀ i j, raw36950step1 i j = -(raw36950step0 i j); unfold raw36950step1 raw36950step0; decide +kernel
      have hl : raw36950step1Labels = raw36950step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36950step1 raw36950step1Labels = mixedMoment B raw36950step2 raw36950step2Labels := by
      have ha : raw36950step2 = raw36950step1 := by apply Matrix.ext; unfold raw36950step2 raw36950step1; decide +kernel
      have hl : raw36950step1Labels = labelEmbedding7 ∘ raw36950step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36950step1 raw36950step1Labels raw36950step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4912 node4912Labels := by rfl

def raw36951 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw36951Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw36951step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36951step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36951step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36951step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36951step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36951step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36951 raw36951Labels = mixedMoment B node5331 node5331Labels := by
  calc
    mixedMoment B raw36951 raw36951Labels = mixedMoment B raw36951step0 raw36951step0Labels := by
      have hz : ∀ j, raw36951 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36951step0 = (fun i j => raw36951 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36951step0 raw36951; decide +kernel
      have hl : raw36951step0Labels = raw36951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36951 raw36951Labels permutation346 hz
    mixedMoment B raw36951step0 raw36951step0Labels = mixedMoment B raw36951step1 raw36951step1Labels := by
      have ha : raw36951step1 = (fun i j => raw36951step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36951step1 raw36951step0; decide +kernel
      have hl : raw36951step1Labels = raw36951step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36951step0 raw36951step0Labels permutation33 permutation4
    mixedMoment B raw36951step1 raw36951step1Labels = mixedMoment B raw36951step2 raw36951step2Labels := by
      have ha : raw36951step2 = -raw36951step1 := by apply Matrix.ext; change ∀ i j, raw36951step2 i j = -(raw36951step1 i j); unfold raw36951step2 raw36951step1; decide +kernel
      have hl : raw36951step2Labels = raw36951step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36951step2 raw36951step2Labels = mixedMoment B raw36951step3 raw36951step3Labels := by
      have ha : raw36951step3 = raw36951step2 := by apply Matrix.ext; unfold raw36951step3 raw36951step2; decide +kernel
      have hl : raw36951step2Labels = labelEmbedding7 ∘ raw36951step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36951step2 raw36951step2Labels raw36951step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5331 node5331Labels := by rfl

def raw36952 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw36952Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw36952step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36952step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36952step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36952step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36952step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36952 raw36952Labels = mixedMoment B node5324 node5324Labels := by
  calc
    mixedMoment B raw36952 raw36952Labels = mixedMoment B raw36952step0 raw36952step0Labels := by
      have ha : raw36952step0 = (fun i j => raw36952 (permutation159 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36952step0 raw36952; decide +kernel
      have hl : raw36952step0Labels = raw36952Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36952 raw36952Labels permutation159 permutation4
    mixedMoment B raw36952step0 raw36952step0Labels = mixedMoment B raw36952step1 raw36952step1Labels := by
      have ha : raw36952step1 = -raw36952step0 := by apply Matrix.ext; change ∀ i j, raw36952step1 i j = -(raw36952step0 i j); unfold raw36952step1 raw36952step0; decide +kernel
      have hl : raw36952step1Labels = raw36952step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36952step1 raw36952step1Labels = mixedMoment B raw36952step2 raw36952step2Labels := by
      have ha : raw36952step2 = raw36952step1 := by apply Matrix.ext; unfold raw36952step2 raw36952step1; decide +kernel
      have hl : raw36952step1Labels = labelEmbedding7 ∘ raw36952step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36952step1 raw36952step1Labels raw36952step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5324 node5324Labels := by rfl

def raw36953 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw36953Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36953step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36953step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36953step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36953 raw36953Labels = mixedMoment B node5326 node5326Labels := by
  calc
    mixedMoment B raw36953 raw36953Labels = mixedMoment B raw36953step0 raw36953step0Labels := by
      have ha : raw36953step0 = (fun i j => raw36953 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36953step0 raw36953; decide +kernel
      have hl : raw36953step0Labels = raw36953Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36953 raw36953Labels permutation152 permutation6
    mixedMoment B raw36953step0 raw36953step0Labels = mixedMoment B raw36953step1 raw36953step1Labels := by
      have ha : raw36953step1 = raw36953step0 := by apply Matrix.ext; unfold raw36953step1 raw36953step0; decide +kernel
      have hl : raw36953step0Labels = labelEmbedding9 ∘ raw36953step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36953step0 raw36953step0Labels raw36953step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5326 node5326Labels := by rfl

def raw36954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36954Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36954step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36954step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36954step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36954step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36954step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36954 raw36954Labels = mixedMoment B node4911 node4911Labels := by
  calc
    mixedMoment B raw36954 raw36954Labels = mixedMoment B raw36954step0 raw36954step0Labels := by
      have ha : raw36954step0 = (fun i j => raw36954 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36954step0 raw36954; decide +kernel
      have hl : raw36954step0Labels = raw36954Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36954 raw36954Labels permutation152 permutation4
    mixedMoment B raw36954step0 raw36954step0Labels = mixedMoment B raw36954step1 raw36954step1Labels := by
      have ha : raw36954step1 = -raw36954step0 := by apply Matrix.ext; change ∀ i j, raw36954step1 i j = -(raw36954step0 i j); unfold raw36954step1 raw36954step0; decide +kernel
      have hl : raw36954step1Labels = raw36954step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36954step1 raw36954step1Labels = mixedMoment B raw36954step2 raw36954step2Labels := by
      have ha : raw36954step2 = raw36954step1 := by apply Matrix.ext; unfold raw36954step2 raw36954step1; decide +kernel
      have hl : raw36954step1Labels = labelEmbedding7 ∘ raw36954step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36954step1 raw36954step1Labels raw36954step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4911 node4911Labels := by rfl

def raw36955 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 3, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36955Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36955step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36955step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36955step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36955step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36955step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36955 raw36955Labels = mixedMoment B node4911 node4911Labels := by
  calc
    mixedMoment B raw36955 raw36955Labels = mixedMoment B raw36955step0 raw36955step0Labels := by
      have ha : raw36955step0 = (fun i j => raw36955 (permutation265 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36955step0 raw36955; decide +kernel
      have hl : raw36955step0Labels = raw36955Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36955 raw36955Labels permutation265 permutation4
    mixedMoment B raw36955step0 raw36955step0Labels = mixedMoment B raw36955step1 raw36955step1Labels := by
      have ha : raw36955step1 = -raw36955step0 := by apply Matrix.ext; change ∀ i j, raw36955step1 i j = -(raw36955step0 i j); unfold raw36955step1 raw36955step0; decide +kernel
      have hl : raw36955step1Labels = raw36955step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36955step1 raw36955step1Labels = mixedMoment B raw36955step2 raw36955step2Labels := by
      have ha : raw36955step2 = raw36955step1 := by apply Matrix.ext; unfold raw36955step2 raw36955step1; decide +kernel
      have hl : raw36955step1Labels = labelEmbedding7 ∘ raw36955step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36955step1 raw36955step1Labels raw36955step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4911 node4911Labels := by rfl

def raw36956 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36956Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36956step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw36956step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36956step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36956step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36956step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36956step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36956 raw36956Labels = mixedMoment B node5323 node5323Labels := by
  calc
    mixedMoment B raw36956 raw36956Labels = mixedMoment B raw36956step0 raw36956step0Labels := by
      have ha : raw36956step0 = (fun i j => raw36956 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36956step0 raw36956; decide +kernel
      have hl : raw36956step0Labels = raw36956Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36956 raw36956Labels permutation158 permutation4
    mixedMoment B raw36956step0 raw36956step0Labels = mixedMoment B raw36956step1 raw36956step1Labels := by
      have ha : raw36956step1 = -raw36956step0 := by apply Matrix.ext; change ∀ i j, raw36956step1 i j = -(raw36956step0 i j); unfold raw36956step1 raw36956step0; decide +kernel
      have hl : raw36956step1Labels = raw36956step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36956step1 raw36956step1Labels = mixedMoment B raw36956step2 raw36956step2Labels := by
      have ha : raw36956step2 = raw36956step1 := by apply Matrix.ext; unfold raw36956step2 raw36956step1; decide +kernel
      have hl : raw36956step1Labels = labelEmbedding7 ∘ raw36956step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36956step1 raw36956step1Labels raw36956step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5323 node5323Labels := by rfl

def raw36957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36957Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36957step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36957 raw36957Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw36957 raw36957Labels = mixedMoment B raw36957step0 raw36957step0Labels := by
      have ha : raw36957step0 = (fun i j => raw36957 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36957step0 raw36957; decide +kernel
      have hl : raw36957step0Labels = raw36957Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36957 raw36957Labels permutation267 permutation2
    _ = mixedMoment B node4996 node4996Labels := by rfl

def raw36958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36958Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36958step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36958step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36958step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36958step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36958step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36958step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36958 raw36958Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw36958 raw36958Labels = mixedMoment B raw36958step0 raw36958step0Labels := by
      have ha : raw36958step0 = (fun i j => raw36958 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36958step0 raw36958; decide +kernel
      have hl : raw36958step0Labels = raw36958Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36958 raw36958Labels permutation277 permutation7
    mixedMoment B raw36958step0 raw36958step0Labels = mixedMoment B raw36958step1 raw36958step1Labels := by
      have ha : raw36958step1 = -raw36958step0 := by apply Matrix.ext; change ∀ i j, raw36958step1 i j = -(raw36958step0 i j); unfold raw36958step1 raw36958step0; decide +kernel
      have hl : raw36958step1Labels = raw36958step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36958step1 raw36958step1Labels = mixedMoment B raw36958step2 raw36958step2Labels := by
      have ha : raw36958step2 = raw36958step1 := by apply Matrix.ext; unfold raw36958step2 raw36958step1; decide +kernel
      have hl : raw36958step1Labels = labelEmbedding10 ∘ raw36958step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36958step1 raw36958step1Labels raw36958step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

def raw36959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36959Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw36959step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36959step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36959step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36959step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36959 raw36959Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw36959 raw36959Labels = mixedMoment B raw36959step0 raw36959step0Labels := by
      have ha : raw36959step0 = (fun i j => raw36959 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36959step0 raw36959; decide +kernel
      have hl : raw36959step0Labels = raw36959Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36959 raw36959Labels permutation277 permutation7
    mixedMoment B raw36959step0 raw36959step0Labels = mixedMoment B raw36959step1 raw36959step1Labels := by
      have ha : raw36959step1 = -raw36959step0 := by apply Matrix.ext; change ∀ i j, raw36959step1 i j = -(raw36959step0 i j); unfold raw36959step1 raw36959step0; decide +kernel
      have hl : raw36959step1Labels = raw36959step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36959step1 raw36959step1Labels = mixedMoment B raw36959step2 raw36959step2Labels := by
      have ha : raw36959step2 = raw36959step1 := by apply Matrix.ext; unfold raw36959step2 raw36959step1; decide +kernel
      have hl : raw36959step1Labels = labelEmbedding10 ∘ raw36959step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36959step1 raw36959step1Labels raw36959step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

def raw36960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36960Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36960step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw36960step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36960step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36960step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36960step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36960step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36960 raw36960Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw36960 raw36960Labels = mixedMoment B raw36960step0 raw36960step0Labels := by
      have hz : ∀ j, raw36960 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36960step0 = (fun i j => raw36960 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36960step0 raw36960; decide +kernel
      have hl : raw36960step0Labels = raw36960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36960 raw36960Labels permutation520 hz
    mixedMoment B raw36960step0 raw36960step0Labels = mixedMoment B raw36960step1 raw36960step1Labels := by
      have ha : raw36960step1 = (fun i j => raw36960step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36960step1 raw36960step0; decide +kernel
      have hl : raw36960step1Labels = raw36960step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36960step0 raw36960step0Labels permutation56 permutation7
    mixedMoment B raw36960step1 raw36960step1Labels = mixedMoment B raw36960step2 raw36960step2Labels := by
      have ha : raw36960step2 = -raw36960step1 := by apply Matrix.ext; change ∀ i j, raw36960step2 i j = -(raw36960step1 i j); unfold raw36960step2 raw36960step1; decide +kernel
      have hl : raw36960step2Labels = raw36960step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36960step2 raw36960step2Labels = mixedMoment B raw36960step3 raw36960step3Labels := by
      have ha : raw36960step3 = raw36960step2 := by apply Matrix.ext; unfold raw36960step3 raw36960step2; decide +kernel
      have hl : raw36960step2Labels = labelEmbedding10 ∘ raw36960step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36960step2 raw36960step2Labels raw36960step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw36961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36961Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36961step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw36961step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36961step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36961step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36961step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36961step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36961 raw36961Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw36961 raw36961Labels = mixedMoment B raw36961step0 raw36961step0Labels := by
      have ha : raw36961step0 = (fun i j => raw36961 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36961step0 raw36961; decide +kernel
      have hl : raw36961step0Labels = raw36961Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36961 raw36961Labels permutation277 permutation7
    mixedMoment B raw36961step0 raw36961step0Labels = mixedMoment B raw36961step1 raw36961step1Labels := by
      have ha : raw36961step1 = -raw36961step0 := by apply Matrix.ext; change ∀ i j, raw36961step1 i j = -(raw36961step0 i j); unfold raw36961step1 raw36961step0; decide +kernel
      have hl : raw36961step1Labels = raw36961step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36961step1 raw36961step1Labels = mixedMoment B raw36961step2 raw36961step2Labels := by
      have ha : raw36961step2 = raw36961step1 := by apply Matrix.ext; unfold raw36961step2 raw36961step1; decide +kernel
      have hl : raw36961step1Labels = labelEmbedding10 ∘ raw36961step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36961step1 raw36961step1Labels raw36961step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw36962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36962Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36962step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36962 raw36962Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw36962 raw36962Labels = mixedMoment B raw36962step0 raw36962step0Labels := by
      have ha : raw36962step0 = (fun i j => raw36962 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36962step0 raw36962; decide +kernel
      have hl : raw36962step0Labels = raw36962Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36962 raw36962Labels permutation154 permutation2
    _ = mixedMoment B node4996 node4996Labels := by rfl

def raw36963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36963Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36963step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw36963step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36963step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36963step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36963step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36963step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36963 raw36963Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw36963 raw36963Labels = mixedMoment B raw36963step0 raw36963step0Labels := by
      have ha : raw36963step0 = (fun i j => raw36963 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36963step0 raw36963; decide +kernel
      have hl : raw36963step0Labels = raw36963Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36963 raw36963Labels permutation164 permutation7
    mixedMoment B raw36963step0 raw36963step0Labels = mixedMoment B raw36963step1 raw36963step1Labels := by
      have ha : raw36963step1 = -raw36963step0 := by apply Matrix.ext; change ∀ i j, raw36963step1 i j = -(raw36963step0 i j); unfold raw36963step1 raw36963step0; decide +kernel
      have hl : raw36963step1Labels = raw36963step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36963step1 raw36963step1Labels = mixedMoment B raw36963step2 raw36963step2Labels := by
      have ha : raw36963step2 = raw36963step1 := by apply Matrix.ext; unfold raw36963step2 raw36963step1; decide +kernel
      have hl : raw36963step1Labels = labelEmbedding10 ∘ raw36963step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36963step1 raw36963step1Labels raw36963step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

def raw36964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36964Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw36964step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36964step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36964step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36964step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36964step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36964 raw36964Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw36964 raw36964Labels = mixedMoment B raw36964step0 raw36964step0Labels := by
      have ha : raw36964step0 = (fun i j => raw36964 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36964step0 raw36964; decide +kernel
      have hl : raw36964step0Labels = raw36964Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36964 raw36964Labels permutation164 permutation7
    mixedMoment B raw36964step0 raw36964step0Labels = mixedMoment B raw36964step1 raw36964step1Labels := by
      have ha : raw36964step1 = -raw36964step0 := by apply Matrix.ext; change ∀ i j, raw36964step1 i j = -(raw36964step0 i j); unfold raw36964step1 raw36964step0; decide +kernel
      have hl : raw36964step1Labels = raw36964step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36964step1 raw36964step1Labels = mixedMoment B raw36964step2 raw36964step2Labels := by
      have ha : raw36964step2 = raw36964step1 := by apply Matrix.ext; unfold raw36964step2 raw36964step1; decide +kernel
      have hl : raw36964step1Labels = labelEmbedding10 ∘ raw36964step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36964step1 raw36964step1Labels raw36964step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

def raw36965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36965Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36965step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw36965step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36965step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36965step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36965step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36965 raw36965Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw36965 raw36965Labels = mixedMoment B raw36965step0 raw36965step0Labels := by
      have hz : ∀ j, raw36965 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36965step0 = (fun i j => raw36965 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36965step0 raw36965; decide +kernel
      have hl : raw36965step0Labels = raw36965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36965 raw36965Labels permutation520 hz
    mixedMoment B raw36965step0 raw36965step0Labels = mixedMoment B raw36965step1 raw36965step1Labels := by
      have ha : raw36965step1 = (fun i j => raw36965step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36965step1 raw36965step0; decide +kernel
      have hl : raw36965step1Labels = raw36965step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36965step0 raw36965step0Labels permutation32 permutation7
    mixedMoment B raw36965step1 raw36965step1Labels = mixedMoment B raw36965step2 raw36965step2Labels := by
      have ha : raw36965step2 = -raw36965step1 := by apply Matrix.ext; change ∀ i j, raw36965step2 i j = -(raw36965step1 i j); unfold raw36965step2 raw36965step1; decide +kernel
      have hl : raw36965step2Labels = raw36965step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36965step2 raw36965step2Labels = mixedMoment B raw36965step3 raw36965step3Labels := by
      have ha : raw36965step3 = raw36965step2 := by apply Matrix.ext; unfold raw36965step3 raw36965step2; decide +kernel
      have hl : raw36965step2Labels = labelEmbedding10 ∘ raw36965step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36965step2 raw36965step2Labels raw36965step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw36966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36966Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36966step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw36966step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36966step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36966step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36966step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36966step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36966 raw36966Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw36966 raw36966Labels = mixedMoment B raw36966step0 raw36966step0Labels := by
      have ha : raw36966step0 = (fun i j => raw36966 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36966step0 raw36966; decide +kernel
      have hl : raw36966step0Labels = raw36966Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36966 raw36966Labels permutation164 permutation7
    mixedMoment B raw36966step0 raw36966step0Labels = mixedMoment B raw36966step1 raw36966step1Labels := by
      have ha : raw36966step1 = -raw36966step0 := by apply Matrix.ext; change ∀ i j, raw36966step1 i j = -(raw36966step0 i j); unfold raw36966step1 raw36966step0; decide +kernel
      have hl : raw36966step1Labels = raw36966step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36966step1 raw36966step1Labels = mixedMoment B raw36966step2 raw36966step2Labels := by
      have ha : raw36966step2 = raw36966step1 := by apply Matrix.ext; unfold raw36966step2 raw36966step1; decide +kernel
      have hl : raw36966step1Labels = labelEmbedding10 ∘ raw36966step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36966step1 raw36966step1Labels raw36966step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw36967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36967Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36967step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36967 raw36967Labels = mixedMoment B node4911 node4911Labels := by
  calc
    mixedMoment B raw36967 raw36967Labels = mixedMoment B raw36967step0 raw36967step0Labels := by
      have ha : raw36967step0 = (fun i j => raw36967 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36967step0 raw36967; decide +kernel
      have hl : raw36967step0Labels = raw36967Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36967 raw36967Labels permutation164 permutation2
    _ = mixedMoment B node4911 node4911Labels := by rfl

def raw36968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36968Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36968step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36968 raw36968Labels = mixedMoment B node4911 node4911Labels := by
  calc
    mixedMoment B raw36968 raw36968Labels = mixedMoment B raw36968step0 raw36968step0Labels := by
      have ha : raw36968step0 = (fun i j => raw36968 (permutation277 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36968step0 raw36968; decide +kernel
      have hl : raw36968step0Labels = raw36968Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36968 raw36968Labels permutation277 permutation2
    _ = mixedMoment B node4911 node4911Labels := by rfl

def raw36969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36969Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36969step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36969 raw36969Labels = mixedMoment B node5323 node5323Labels := by
  calc
    mixedMoment B raw36969 raw36969Labels = mixedMoment B raw36969step0 raw36969step0Labels := by
      have ha : raw36969step0 = (fun i j => raw36969 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36969step0 raw36969; decide +kernel
      have hl : raw36969step0Labels = raw36969Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36969 raw36969Labels permutation160 permutation2
    _ = mixedMoment B node5323 node5323Labels := by rfl

def raw36970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36970Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36970step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36970step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw36970step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw36970step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw36970step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical36970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36970 raw36970Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw36970 raw36970Labels = mixedMoment B raw36970step0 raw36970step0Labels := by
      have hz : ∀ j, raw36970 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36970step0 = (fun i j => raw36970 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36970step0 raw36970; decide +kernel
      have hl : raw36970step0Labels = raw36970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36970 raw36970Labels permutation520 hz
    mixedMoment B raw36970step0 raw36970step0Labels = mixedMoment B raw36970step1 raw36970step1Labels := by
      have hz : ∀ i, raw36970step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw36970step1 = (fun i j => raw36970step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw36970step1 raw36970step0; decide +kernel
      have hl : raw36970step1Labels = (fun j => raw36970step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw36970step0 raw36970step0Labels permutation4 hz
    mixedMoment B raw36970step1 raw36970step1Labels = mixedMoment B raw36970step2 raw36970step2Labels := by
      have ha : raw36970step2 = raw36970step1 := by apply Matrix.ext; unfold raw36970step2 raw36970step1; decide +kernel
      have hl : raw36970step1Labels = labelEmbedding2 ∘ raw36970step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36970step1 raw36970step1Labels raw36970step2Labels labelEmbedding2 hl
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw36971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36971Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36971step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36971step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36971step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36971step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36971step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36971 raw36971Labels = mixedMoment B node5325 node5325Labels := by
  calc
    mixedMoment B raw36971 raw36971Labels = mixedMoment B raw36971step0 raw36971step0Labels := by
      have ha : raw36971step0 = (fun i j => raw36971 (permutation164 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36971step0 raw36971; decide +kernel
      have hl : raw36971step0Labels = raw36971Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36971 raw36971Labels permutation164 permutation7
    mixedMoment B raw36971step0 raw36971step0Labels = mixedMoment B raw36971step1 raw36971step1Labels := by
      have ha : raw36971step1 = -raw36971step0 := by apply Matrix.ext; change ∀ i j, raw36971step1 i j = -(raw36971step0 i j); unfold raw36971step1 raw36971step0; decide +kernel
      have hl : raw36971step1Labels = raw36971step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36971step1 raw36971step1Labels = mixedMoment B raw36971step2 raw36971step2Labels := by
      have ha : raw36971step2 = raw36971step1 := by apply Matrix.ext; unfold raw36971step2 raw36971step1; decide +kernel
      have hl : raw36971step1Labels = labelEmbedding10 ∘ raw36971step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36971step1 raw36971step1Labels raw36971step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5325 node5325Labels := by rfl

def raw36972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36972Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36972step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36972 raw36972Labels = mixedMoment B node4903 node4903Labels := by
  calc
    mixedMoment B raw36972 raw36972Labels = mixedMoment B raw36972step0 raw36972step0Labels := by
      have ha : raw36972step0 = (fun i j => raw36972 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36972step0 raw36972; decide +kernel
      have hl : raw36972step0Labels = raw36972Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36972 raw36972Labels permutation154 permutation2
    _ = mixedMoment B node4903 node4903Labels := by rfl

def raw36973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36973Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36973step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36973 raw36973Labels = mixedMoment B node4903 node4903Labels := by
  calc
    mixedMoment B raw36973 raw36973Labels = mixedMoment B raw36973step0 raw36973step0Labels := by
      have ha : raw36973step0 = (fun i j => raw36973 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36973step0 raw36973; decide +kernel
      have hl : raw36973step0Labels = raw36973Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36973 raw36973Labels permutation267 permutation2
    _ = mixedMoment B node4903 node4903Labels := by rfl

def raw36974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw36974Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36974step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36974 raw36974Labels = mixedMoment B node5317 node5317Labels := by
  calc
    mixedMoment B raw36974 raw36974Labels = mixedMoment B raw36974step0 raw36974step0Labels := by
      have ha : raw36974step0 = (fun i j => raw36974 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36974step0 raw36974; decide +kernel
      have hl : raw36974step0Labels = raw36974Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36974 raw36974Labels permutation154 permutation2
    _ = mixedMoment B node5317 node5317Labels := by rfl

def raw36975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw36975Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw36975step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36975 raw36975Labels = mixedMoment B node5327 node5327Labels := by
  calc
    mixedMoment B raw36975 raw36975Labels = mixedMoment B raw36975step0 raw36975step0Labels := by
      have hz : ∀ j, raw36975 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36975step0 = (fun i j => raw36975 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36975step0 raw36975; decide +kernel
      have hl : raw36975step0Labels = raw36975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36975 raw36975Labels permutation520 hz
    _ = mixedMoment B node5327 node5327Labels := by rfl

def raw36976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw36976Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36976step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36976 raw36976Labels = mixedMoment B node5324 node5324Labels := by
  calc
    mixedMoment B raw36976 raw36976Labels = mixedMoment B raw36976step0 raw36976step0Labels := by
      have ha : raw36976step0 = (fun i j => raw36976 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36976step0 raw36976; decide +kernel
      have hl : raw36976step0Labels = raw36976Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36976 raw36976Labels permutation155 permutation2
    _ = mixedMoment B node5324 node5324Labels := by rfl

def raw36977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36977Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36977 raw36977Labels = mixedMoment B node4905 node4905Labels := by
  calc
    _ = mixedMoment B node4905 node4905Labels := by rfl

def raw36978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36978Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36978step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36978 raw36978Labels = mixedMoment B node4905 node4905Labels := by
  calc
    mixedMoment B raw36978 raw36978Labels = mixedMoment B raw36978step0 raw36978step0Labels := by
      have ha : raw36978step0 = (fun i j => raw36978 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36978step0 raw36978; decide +kernel
      have hl : raw36978step0Labels = raw36978Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36978 raw36978Labels permutation265 permutation2
    _ = mixedMoment B node4905 node4905Labels := by rfl

def raw36979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36979Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36979 raw36979Labels = mixedMoment B node5318 node5318Labels := by
  calc
    _ = mixedMoment B node5318 node5318Labels := by rfl

def raw36980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36980Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36980 raw36980Labels = mixedMoment B node5320 node5320Labels := by
  calc
    _ = mixedMoment B node5320 node5320Labels := by rfl

def raw36981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw36981Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36981step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36981step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36981 raw36981Labels = mixedMoment B node5326 node5326Labels := by
  calc
    mixedMoment B raw36981 raw36981Labels = mixedMoment B raw36981step0 raw36981step0Labels := by
      have ha : raw36981step0 = (fun i j => raw36981 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36981step0 raw36981; decide +kernel
      have hl : raw36981step0Labels = raw36981Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36981 raw36981Labels permutation153 permutation2
    _ = mixedMoment B node5326 node5326Labels := by rfl

def raw36982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36982Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw36982step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36982 raw36982Labels = mixedMoment B node4902 node4902Labels := by
  calc
    mixedMoment B raw36982 raw36982Labels = mixedMoment B raw36982step0 raw36982step0Labels := by
      have ha : raw36982step0 = (fun i j => raw36982 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36982step0 raw36982; decide +kernel
      have hl : raw36982step0Labels = raw36982Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36982 raw36982Labels permutation154 permutation2
    _ = mixedMoment B node4902 node4902Labels := by rfl

def raw36983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36983Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw36983step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36983 raw36983Labels = mixedMoment B node4902 node4902Labels := by
  calc
    mixedMoment B raw36983 raw36983Labels = mixedMoment B raw36983step0 raw36983step0Labels := by
      have ha : raw36983step0 = (fun i j => raw36983 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36983step0 raw36983; decide +kernel
      have hl : raw36983step0Labels = raw36983Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36983 raw36983Labels permutation267 permutation2
    _ = mixedMoment B node4902 node4902Labels := by rfl

def raw36984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 2, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw36984step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36984step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw36984step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36984 raw36984Labels = mixedMoment B node5032 node5032Labels := by
  calc
    mixedMoment B raw36984 raw36984Labels = mixedMoment B raw36984step0 raw36984step0Labels := by
      have ha : raw36984step0 = (fun i j => raw36984 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36984step0 raw36984; decide +kernel
      have hl : raw36984step0Labels = raw36984Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36984 raw36984Labels permutation663 permutation2
    mixedMoment B raw36984step0 raw36984step0Labels = mixedMoment B raw36984step1 raw36984step1Labels := by
      have ha : raw36984step1 = -raw36984step0 := by apply Matrix.ext; change ∀ i j, raw36984step1 i j = -(raw36984step0 i j); unfold raw36984step1 raw36984step0; decide +kernel
      have hl : raw36984step1Labels = raw36984step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5032 node5032Labels := by rfl

def raw36985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw36985step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36985step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw36985step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36985 raw36985Labels = mixedMoment B node5126 node5126Labels := by
  calc
    mixedMoment B raw36985 raw36985Labels = mixedMoment B raw36985step0 raw36985step0Labels := by
      have ha : raw36985step0 = (fun i j => raw36985 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36985step0 raw36985; decide +kernel
      have hl : raw36985step0Labels = raw36985Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36985 raw36985Labels permutation681 permutation2
    mixedMoment B raw36985step0 raw36985step0Labels = mixedMoment B raw36985step1 raw36985step1Labels := by
      have ha : raw36985step1 = -raw36985step0 := by apply Matrix.ext; change ∀ i j, raw36985step1 i j = -(raw36985step0 i j); unfold raw36985step1 raw36985step0; decide +kernel
      have hl : raw36985step1Labels = raw36985step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5126 node5126Labels := by rfl

def raw36986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw36986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw36986step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw36986step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36986step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw36986step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36986 raw36986Labels = mixedMoment B node5063 node5063Labels := by
  calc
    mixedMoment B raw36986 raw36986Labels = mixedMoment B raw36986step0 raw36986step0Labels := by
      have hz : ∀ j, raw36986 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36986step0 = (fun i j => raw36986 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36986step0 raw36986; decide +kernel
      have hl : raw36986step0Labels = raw36986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36986 raw36986Labels permutation520 hz
    mixedMoment B raw36986step0 raw36986step0Labels = mixedMoment B raw36986step1 raw36986step1Labels := by
      have ha : raw36986step1 = (fun i j => raw36986step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36986step1 raw36986step0; decide +kernel
      have hl : raw36986step1Labels = raw36986step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36986step0 raw36986step0Labels permutation150 permutation2
    mixedMoment B raw36986step1 raw36986step1Labels = mixedMoment B raw36986step2 raw36986step2Labels := by
      have ha : raw36986step2 = -raw36986step1 := by apply Matrix.ext; change ∀ i j, raw36986step2 i j = -(raw36986step1 i j); unfold raw36986step2 raw36986step1; decide +kernel
      have hl : raw36986step2Labels = raw36986step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5063 node5063Labels := by rfl

def raw36987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36987step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36987step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36987 raw36987Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw36987 raw36987Labels = mixedMoment B raw36987step0 raw36987step0Labels := by
      have hz : ∀ j, raw36987 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36987step0 = (fun i j => raw36987 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36987step0 raw36987; decide +kernel
      have hl : raw36987step0Labels = raw36987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36987 raw36987Labels permutation346 hz
    mixedMoment B raw36987step0 raw36987step0Labels = mixedMoment B raw36987step1 raw36987step1Labels := by
      have ha : raw36987step1 = (fun i j => raw36987step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36987step1 raw36987step0; decide +kernel
      have hl : raw36987step1Labels = raw36987step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36987step0 raw36987step0Labels permutation58 permutation2
    _ = mixedMoment B node5018 node5018Labels := by rfl

def raw36988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36988step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36988step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36988step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36988step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36988step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36988 raw36988Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw36988 raw36988Labels = mixedMoment B raw36988step0 raw36988step0Labels := by
      have ha : raw36988step0 = (fun i j => raw36988 (permutation268 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36988step0 raw36988; decide +kernel
      have hl : raw36988step0Labels = raw36988Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36988 raw36988Labels permutation268 permutation7
    mixedMoment B raw36988step0 raw36988step0Labels = mixedMoment B raw36988step1 raw36988step1Labels := by
      have ha : raw36988step1 = -raw36988step0 := by apply Matrix.ext; change ∀ i j, raw36988step1 i j = -(raw36988step0 i j); unfold raw36988step1 raw36988step0; decide +kernel
      have hl : raw36988step1Labels = raw36988step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36988step1 raw36988step1Labels = mixedMoment B raw36988step2 raw36988step2Labels := by
      have ha : raw36988step2 = raw36988step1 := by apply Matrix.ext; unfold raw36988step2 raw36988step1; decide +kernel
      have hl : raw36988step1Labels = labelEmbedding10 ∘ raw36988step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36988step1 raw36988step1Labels raw36988step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

def raw36989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36989step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw36989step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36989step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36989step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36989step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36989step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36989 raw36989Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw36989 raw36989Labels = mixedMoment B raw36989step0 raw36989step0Labels := by
      have hz : ∀ j, raw36989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36989step0 = (fun i j => raw36989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36989step0 raw36989; decide +kernel
      have hl : raw36989step0Labels = raw36989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36989 raw36989Labels permutation346 hz
    mixedMoment B raw36989step0 raw36989step0Labels = mixedMoment B raw36989step1 raw36989step1Labels := by
      have ha : raw36989step1 = (fun i j => raw36989step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36989step1 raw36989step0; decide +kernel
      have hl : raw36989step1Labels = raw36989step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36989step0 raw36989step0Labels permutation59 permutation7
    mixedMoment B raw36989step1 raw36989step1Labels = mixedMoment B raw36989step2 raw36989step2Labels := by
      have ha : raw36989step2 = -raw36989step1 := by apply Matrix.ext; change ∀ i j, raw36989step2 i j = -(raw36989step1 i j); unfold raw36989step2 raw36989step1; decide +kernel
      have hl : raw36989step2Labels = raw36989step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36989step2 raw36989step2Labels = mixedMoment B raw36989step3 raw36989step3Labels := by
      have ha : raw36989step3 = raw36989step2 := by apply Matrix.ext; unfold raw36989step3 raw36989step2; decide +kernel
      have hl : raw36989step2Labels = labelEmbedding10 ∘ raw36989step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36989step2 raw36989step2Labels raw36989step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw36990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -1, -1]]
def raw36990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 0, 2], ![1, 1, -2], ![0, 1, -1], ![2, -1, -1]]
def raw36990step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw36990step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36990step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36990step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36990step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36990step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36990 raw36990Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw36990 raw36990Labels = mixedMoment B raw36990step0 raw36990step0Labels := by
      have hz : ∀ j, raw36990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36990step0 = (fun i j => raw36990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36990step0 raw36990; decide +kernel
      have hl : raw36990step0Labels = raw36990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36990 raw36990Labels permutation346 hz
    mixedMoment B raw36990step0 raw36990step0Labels = mixedMoment B raw36990step1 raw36990step1Labels := by
      have ha : raw36990step1 = (fun i j => raw36990step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36990step1 raw36990step0; decide +kernel
      have hl : raw36990step1Labels = raw36990step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36990step0 raw36990step0Labels permutation59 permutation7
    mixedMoment B raw36990step1 raw36990step1Labels = mixedMoment B raw36990step2 raw36990step2Labels := by
      have ha : raw36990step2 = -raw36990step1 := by apply Matrix.ext; change ∀ i j, raw36990step2 i j = -(raw36990step1 i j); unfold raw36990step2 raw36990step1; decide +kernel
      have hl : raw36990step2Labels = raw36990step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36990step2 raw36990step2Labels = mixedMoment B raw36990step3 raw36990step3Labels := by
      have ha : raw36990step3 = raw36990step2 := by apply Matrix.ext; unfold raw36990step3 raw36990step2; decide +kernel
      have hl : raw36990step2Labels = labelEmbedding10 ∘ raw36990step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36990step2 raw36990step2Labels raw36990step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw36991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw36991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 0, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw36991step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36991step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36991step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36991step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36991step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36991step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36991 raw36991Labels = mixedMoment B node5369 node5369Labels := by
  calc
    mixedMoment B raw36991 raw36991Labels = mixedMoment B raw36991step0 raw36991step0Labels := by
      have hz : ∀ j, raw36991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36991step0 = (fun i j => raw36991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36991step0 raw36991; decide +kernel
      have hl : raw36991step0Labels = raw36991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36991 raw36991Labels permutation346 hz
    mixedMoment B raw36991step0 raw36991step0Labels = mixedMoment B raw36991step1 raw36991step1Labels := by
      have ha : raw36991step1 = (fun i j => raw36991step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36991step1 raw36991step0; decide +kernel
      have hl : raw36991step1Labels = raw36991step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36991step0 raw36991step0Labels permutation59 permutation7
    mixedMoment B raw36991step1 raw36991step1Labels = mixedMoment B raw36991step2 raw36991step2Labels := by
      have ha : raw36991step2 = -raw36991step1 := by apply Matrix.ext; change ∀ i j, raw36991step2 i j = -(raw36991step1 i j); unfold raw36991step2 raw36991step1; decide +kernel
      have hl : raw36991step2Labels = raw36991step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36991step2 raw36991step2Labels = mixedMoment B raw36991step3 raw36991step3Labels := by
      have ha : raw36991step3 = raw36991step2 := by apply Matrix.ext; unfold raw36991step3 raw36991step2; decide +kernel
      have hl : raw36991step2Labels = labelEmbedding10 ∘ raw36991step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36991step2 raw36991step2Labels raw36991step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5369 node5369Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
