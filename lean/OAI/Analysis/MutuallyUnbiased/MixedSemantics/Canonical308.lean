import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes3
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes4
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes5
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes6
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.ExtraNodes

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw39424 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw39424Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39424step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw39424step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39424 raw39424Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw39424 raw39424Labels = mixedMoment B raw39424step0 raw39424step0Labels := by
      have ha : raw39424step0 = raw39424 := by apply Matrix.ext; unfold raw39424step0 raw39424; decide +kernel
      have hl : raw39424Labels = labelEmbedding2 ∘ raw39424step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39424 raw39424Labels raw39424step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3963 node3963Labels := by rfl

def raw39425 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw39425Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39425step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw39425step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39425step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw39425step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39425 raw39425Labels = mixedMoment B node3963 node3963Labels := by
  calc
    mixedMoment B raw39425 raw39425Labels = mixedMoment B raw39425step0 raw39425step0Labels := by
      have ha : raw39425step0 = (fun i j => raw39425 (permutation24 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39425step0 raw39425; decide +kernel
      have hl : raw39425step0Labels = raw39425Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39425 raw39425Labels permutation24 permutation7
    mixedMoment B raw39425step0 raw39425step0Labels = mixedMoment B raw39425step1 raw39425step1Labels := by
      have ha : raw39425step1 = raw39425step0 := by apply Matrix.ext; unfold raw39425step1 raw39425step0; decide +kernel
      have hl : raw39425step0Labels = labelEmbedding4 ∘ raw39425step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39425step0 raw39425step0Labels raw39425step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3963 node3963Labels := by rfl

def raw39426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39426Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39426 raw39426Labels = mixedMoment B node3965 node3965Labels := by
  calc
    mixedMoment B raw39426 raw39426Labels = mixedMoment B raw39426step0 raw39426step0Labels := by
      have ha : raw39426step0 = raw39426 := by apply Matrix.ext; unfold raw39426step0 raw39426; decide +kernel
      have hl : raw39426Labels = labelEmbedding2 ∘ raw39426step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39426 raw39426Labels raw39426step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3965 node3965Labels := by rfl

def raw39427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39427Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39427step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39427step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39427step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39427 raw39427Labels = mixedMoment B node4045 node4045Labels := by
  calc
    mixedMoment B raw39427 raw39427Labels = mixedMoment B raw39427step0 raw39427step0Labels := by
      have ha : raw39427step0 = (fun i j => raw39427 (permutation662 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39427step0 raw39427; decide +kernel
      have hl : raw39427step0Labels = raw39427Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39427 raw39427Labels permutation662 permutation5
    mixedMoment B raw39427step0 raw39427step0Labels = mixedMoment B raw39427step1 raw39427step1Labels := by
      have ha : raw39427step1 = raw39427step0 := by apply Matrix.ext; unfold raw39427step1 raw39427step0; decide +kernel
      have hl : raw39427step0Labels = labelEmbedding4 ∘ raw39427step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39427step0 raw39427step0Labels raw39427step1Labels labelEmbedding4 hl
    _ = mixedMoment B node4045 node4045Labels := by rfl

def raw39428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39428Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39428 raw39428Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw39428 raw39428Labels = mixedMoment B raw39428step0 raw39428step0Labels := by
      have ha : raw39428step0 = raw39428 := by apply Matrix.ext; unfold raw39428step0 raw39428; decide +kernel
      have hl : raw39428Labels = labelEmbedding2 ∘ raw39428step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39428 raw39428Labels raw39428step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw39429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39429Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39429step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39429step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39429 raw39429Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw39429 raw39429Labels = mixedMoment B raw39429step0 raw39429step0Labels := by
      have ha : raw39429step0 = (fun i j => raw39429 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39429step0 raw39429; decide +kernel
      have hl : raw39429step0Labels = raw39429Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39429 raw39429Labels permutation688 permutation7
    mixedMoment B raw39429step0 raw39429step0Labels = mixedMoment B raw39429step1 raw39429step1Labels := by
      have ha : raw39429step1 = raw39429step0 := by apply Matrix.ext; unfold raw39429step1 raw39429step0; decide +kernel
      have hl : raw39429step0Labels = labelEmbedding4 ∘ raw39429step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39429step0 raw39429step0Labels raw39429step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw39430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39430Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39430step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39430 raw39430Labels = mixedMoment B node3980 node3980Labels := by
  calc
    mixedMoment B raw39430 raw39430Labels = mixedMoment B raw39430step0 raw39430step0Labels := by
      have ha : raw39430step0 = raw39430 := by apply Matrix.ext; unfold raw39430step0 raw39430; decide +kernel
      have hl : raw39430Labels = labelEmbedding2 ∘ raw39430step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39430 raw39430Labels raw39430step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3980 node3980Labels := by rfl

def raw39431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39431Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw39431step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39431step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw39431step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39431step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw39431step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39431 raw39431Labels = mixedMoment B node4046 node4046Labels := by
  calc
    mixedMoment B raw39431 raw39431Labels = mixedMoment B raw39431step0 raw39431step0Labels := by
      have ha : raw39431step0 = (fun i j => raw39431 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39431step0 raw39431; decide +kernel
      have hl : raw39431step0Labels = raw39431Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39431 raw39431Labels permutation160 permutation7
    mixedMoment B raw39431step0 raw39431step0Labels = mixedMoment B raw39431step1 raw39431step1Labels := by
      have ha : raw39431step1 = -raw39431step0 := by apply Matrix.ext; change ∀ i j, raw39431step1 i j = -(raw39431step0 i j); unfold raw39431step1 raw39431step0; decide +kernel
      have hl : raw39431step1Labels = raw39431step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39431step1 raw39431step1Labels = mixedMoment B raw39431step2 raw39431step2Labels := by
      have ha : raw39431step2 = raw39431step1 := by apply Matrix.ext; unfold raw39431step2 raw39431step1; decide +kernel
      have hl : raw39431step1Labels = labelEmbedding4 ∘ raw39431step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39431step1 raw39431step1Labels raw39431step2Labels labelEmbedding4 hl
    _ = mixedMoment B node4046 node4046Labels := by rfl

def raw39432 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39432Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39432 raw39432Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw39432 raw39432Labels = mixedMoment B raw39432step0 raw39432step0Labels := by
      have ha : raw39432step0 = raw39432 := by apply Matrix.ext; unfold raw39432step0 raw39432; decide +kernel
      have hl : raw39432Labels = labelEmbedding2 ∘ raw39432step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39432 raw39432Labels raw39432step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw39433 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39433Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw39433step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39433step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw39433step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39433 raw39433Labels = mixedMoment B node4047 node4047Labels := by
  calc
    mixedMoment B raw39433 raw39433Labels = mixedMoment B raw39433step0 raw39433step0Labels := by
      have ha : raw39433step0 = (fun i j => raw39433 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39433step0 raw39433; decide +kernel
      have hl : raw39433step0Labels = raw39433Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39433 raw39433Labels permutation149 permutation5
    mixedMoment B raw39433step0 raw39433step0Labels = mixedMoment B raw39433step1 raw39433step1Labels := by
      have ha : raw39433step1 = raw39433step0 := by apply Matrix.ext; unfold raw39433step1 raw39433step0; decide +kernel
      have hl : raw39433step0Labels = labelEmbedding4 ∘ raw39433step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39433step0 raw39433step0Labels raw39433step1Labels labelEmbedding4 hl
    _ = mixedMoment B node4047 node4047Labels := by rfl

def raw39434 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw39434Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw39434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39434 raw39434Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw39434 raw39434Labels = mixedMoment B raw39434step0 raw39434step0Labels := by
      have ha : raw39434step0 = raw39434 := by apply Matrix.ext; unfold raw39434step0 raw39434; decide +kernel
      have hl : raw39434Labels = labelEmbedding2 ∘ raw39434step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39434 raw39434Labels raw39434step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw39435 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw39435Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw39435step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw39435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39435 raw39435Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw39435 raw39435Labels = mixedMoment B raw39435step0 raw39435step0Labels := by
      have ha : raw39435step0 = (fun i j => raw39435 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39435step0 raw39435; decide +kernel
      have hl : raw39435step0Labels = raw39435Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39435 raw39435Labels permutation151 permutation7
    mixedMoment B raw39435step0 raw39435step0Labels = mixedMoment B raw39435step1 raw39435step1Labels := by
      have ha : raw39435step1 = raw39435step0 := by apply Matrix.ext; unfold raw39435step1 raw39435step0; decide +kernel
      have hl : raw39435step0Labels = labelEmbedding4 ∘ raw39435step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39435step0 raw39435step0Labels raw39435step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw39436 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw39436Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw39436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39436 raw39436Labels = mixedMoment B node3984 node3984Labels := by
  calc
    mixedMoment B raw39436 raw39436Labels = mixedMoment B raw39436step0 raw39436step0Labels := by
      have ha : raw39436step0 = raw39436 := by apply Matrix.ext; unfold raw39436step0 raw39436; decide +kernel
      have hl : raw39436Labels = labelEmbedding2 ∘ raw39436step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39436 raw39436Labels raw39436step0Labels labelEmbedding2 hl
    _ = mixedMoment B node3984 node3984Labels := by rfl

def raw39437 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw39437Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw39437step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw39437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39437 raw39437Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw39437 raw39437Labels = mixedMoment B raw39437step0 raw39437step0Labels := by
      have ha : raw39437step0 = (fun i j => raw39437 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39437step0 raw39437; decide +kernel
      have hl : raw39437step0Labels = raw39437Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39437 raw39437Labels permutation145 permutation7
    mixedMoment B raw39437step0 raw39437step0Labels = mixedMoment B raw39437step1 raw39437step1Labels := by
      have ha : raw39437step1 = raw39437step0 := by apply Matrix.ext; unfold raw39437step1 raw39437step0; decide +kernel
      have hl : raw39437step0Labels = labelEmbedding4 ∘ raw39437step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39437step0 raw39437step0Labels raw39437step1Labels labelEmbedding4 hl
    _ = mixedMoment B node4010 node4010Labels := by rfl

def raw39438 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw39438Labels : Fin 3 → Fin 3 := ![1, 1, 2]

def raw39438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw39438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39438 raw39438Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw39438 raw39438Labels = mixedMoment B raw39438step0 raw39438step0Labels := by
      have ha : raw39438step0 = raw39438 := by apply Matrix.ext; unfold raw39438step0 raw39438; decide +kernel
      have hl : raw39438Labels = labelEmbedding3 ∘ raw39438step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39438 raw39438Labels raw39438step0Labels labelEmbedding3 hl
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw39439 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw39439Labels : Fin 3 → Fin 3 := ![2, 1, 2]

def raw39439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw39439step0Labels : Fin 3 → Fin 3 := ![2, 2, 1]

def raw39439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw39439step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39439 raw39439Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw39439 raw39439Labels = mixedMoment B raw39439step0 raw39439step0Labels := by
      have ha : raw39439step0 = (fun i j => raw39439 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39439step0 raw39439; decide +kernel
      have hl : raw39439step0Labels = raw39439Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39439 raw39439Labels permutation39 permutation3
    mixedMoment B raw39439step0 raw39439step0Labels = mixedMoment B raw39439step1 raw39439step1Labels := by
      have ha : raw39439step1 = raw39439step0 := by apply Matrix.ext; unfold raw39439step1 raw39439step0; decide +kernel
      have hl : raw39439step0Labels = labelEmbedding5 ∘ raw39439step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39439step0 raw39439step0Labels raw39439step1Labels labelEmbedding5 hl
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw39440 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw39440Labels : Fin 3 → Fin 3 := ![1, 1, 2]

def raw39440step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw39440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39440 raw39440Labels = mixedMoment B node4014 node4014Labels := by
  calc
    mixedMoment B raw39440 raw39440Labels = mixedMoment B raw39440step0 raw39440step0Labels := by
      have ha : raw39440step0 = raw39440 := by apply Matrix.ext; unfold raw39440step0 raw39440; decide +kernel
      have hl : raw39440Labels = labelEmbedding3 ∘ raw39440step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39440 raw39440Labels raw39440step0Labels labelEmbedding3 hl
    _ = mixedMoment B node4014 node4014Labels := by rfl

def raw39441 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw39441Labels : Fin 3 → Fin 3 := ![2, 1, 2]

def raw39441step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw39441step0Labels : Fin 3 → Fin 3 := ![2, 2, 1]

def raw39441step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw39441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39441 raw39441Labels = mixedMoment B node4014 node4014Labels := by
  calc
    mixedMoment B raw39441 raw39441Labels = mixedMoment B raw39441step0 raw39441step0Labels := by
      have ha : raw39441step0 = (fun i j => raw39441 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39441step0 raw39441; decide +kernel
      have hl : raw39441step0Labels = raw39441Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39441 raw39441Labels permutation10 permutation3
    mixedMoment B raw39441step0 raw39441step0Labels = mixedMoment B raw39441step1 raw39441step1Labels := by
      have ha : raw39441step1 = raw39441step0 := by apply Matrix.ext; unfold raw39441step1 raw39441step0; decide +kernel
      have hl : raw39441step0Labels = labelEmbedding5 ∘ raw39441step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39441step0 raw39441step0Labels raw39441step1Labels labelEmbedding5 hl
    _ = mixedMoment B node4014 node4014Labels := by rfl

def raw39442 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw39442Labels : Fin 3 → Fin 3 := ![1, 1, 2]

def raw39442step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw39442step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39442 raw39442Labels = mixedMoment B node4015 node4015Labels := by
  calc
    mixedMoment B raw39442 raw39442Labels = mixedMoment B raw39442step0 raw39442step0Labels := by
      have ha : raw39442step0 = raw39442 := by apply Matrix.ext; unfold raw39442step0 raw39442; decide +kernel
      have hl : raw39442Labels = labelEmbedding3 ∘ raw39442step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39442 raw39442Labels raw39442step0Labels labelEmbedding3 hl
    _ = mixedMoment B node4015 node4015Labels := by rfl

def raw39443 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw39443Labels : Fin 3 → Fin 3 := ![2, 1, 2]

def raw39443step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw39443step0Labels : Fin 3 → Fin 3 := ![2, 2, 1]

def raw39443step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw39443step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39443 raw39443Labels = mixedMoment B node4017 node4017Labels := by
  calc
    mixedMoment B raw39443 raw39443Labels = mixedMoment B raw39443step0 raw39443step0Labels := by
      have ha : raw39443step0 = (fun i j => raw39443 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39443step0 raw39443; decide +kernel
      have hl : raw39443step0Labels = raw39443Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39443 raw39443Labels permutation9 permutation3
    mixedMoment B raw39443step0 raw39443step0Labels = mixedMoment B raw39443step1 raw39443step1Labels := by
      have ha : raw39443step1 = raw39443step0 := by apply Matrix.ext; unfold raw39443step1 raw39443step0; decide +kernel
      have hl : raw39443step0Labels = labelEmbedding5 ∘ raw39443step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39443step0 raw39443step0Labels raw39443step1Labels labelEmbedding5 hl
    _ = mixedMoment B node4017 node4017Labels := by rfl

def raw39444 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw39444Labels : Fin 3 → Fin 3 := ![1, 1, 2]

def raw39444step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw39444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39444 raw39444Labels = mixedMoment B node4020 node4020Labels := by
  calc
    mixedMoment B raw39444 raw39444Labels = mixedMoment B raw39444step0 raw39444step0Labels := by
      have ha : raw39444step0 = raw39444 := by apply Matrix.ext; unfold raw39444step0 raw39444; decide +kernel
      have hl : raw39444Labels = labelEmbedding3 ∘ raw39444step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39444 raw39444Labels raw39444step0Labels labelEmbedding3 hl
    _ = mixedMoment B node4020 node4020Labels := by rfl

def raw39445 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw39445Labels : Fin 3 → Fin 3 := ![2, 1, 2]

def raw39445step0 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw39445step0Labels : Fin 3 → Fin 3 := ![2, 2, 1]

def raw39445step1 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 1, -2]]
def raw39445step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39445 raw39445Labels = mixedMoment B node4020 node4020Labels := by
  calc
    mixedMoment B raw39445 raw39445Labels = mixedMoment B raw39445step0 raw39445step0Labels := by
      have ha : raw39445step0 = (fun i j => raw39445 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39445step0 raw39445; decide +kernel
      have hl : raw39445step0Labels = raw39445Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39445 raw39445Labels permutation3 permutation3
    mixedMoment B raw39445step0 raw39445step0Labels = mixedMoment B raw39445step1 raw39445step1Labels := by
      have ha : raw39445step1 = raw39445step0 := by apply Matrix.ext; unfold raw39445step1 raw39445step0; decide +kernel
      have hl : raw39445step0Labels = labelEmbedding5 ∘ raw39445step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39445step0 raw39445step0Labels raw39445step1Labels labelEmbedding5 hl
    _ = mixedMoment B node4020 node4020Labels := by rfl

def raw39446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39446Labels : Fin 3 → Fin 3 := ![1, 1, 2]

def raw39446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39446 raw39446Labels = mixedMoment B node4051 node4051Labels := by
  calc
    mixedMoment B raw39446 raw39446Labels = mixedMoment B raw39446step0 raw39446step0Labels := by
      have ha : raw39446step0 = raw39446 := by apply Matrix.ext; unfold raw39446step0 raw39446; decide +kernel
      have hl : raw39446Labels = labelEmbedding3 ∘ raw39446step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39446 raw39446Labels raw39446step0Labels labelEmbedding3 hl
    _ = mixedMoment B node4051 node4051Labels := by rfl

def raw39447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39447Labels : Fin 3 → Fin 3 := ![2, 1, 2]

def raw39447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw39447step0Labels : Fin 3 → Fin 3 := ![2, 2, 1]

def raw39447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39447step1Labels : Fin 3 → Fin 3 := ![2, 2, 1]

def raw39447step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39447step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39447 raw39447Labels = mixedMoment B node4051 node4051Labels := by
  calc
    mixedMoment B raw39447 raw39447Labels = mixedMoment B raw39447step0 raw39447step0Labels := by
      have ha : raw39447step0 = (fun i j => raw39447 (permutation583 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39447step0 raw39447; decide +kernel
      have hl : raw39447step0Labels = raw39447Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39447 raw39447Labels permutation583 permutation3
    mixedMoment B raw39447step0 raw39447step0Labels = mixedMoment B raw39447step1 raw39447step1Labels := by
      have ha : raw39447step1 = -raw39447step0 := by apply Matrix.ext; change ∀ i j, raw39447step1 i j = -(raw39447step0 i j); unfold raw39447step1 raw39447step0; decide +kernel
      have hl : raw39447step1Labels = raw39447step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39447step1 raw39447step1Labels = mixedMoment B raw39447step2 raw39447step2Labels := by
      have ha : raw39447step2 = raw39447step1 := by apply Matrix.ext; unfold raw39447step2 raw39447step1; decide +kernel
      have hl : raw39447step1Labels = labelEmbedding5 ∘ raw39447step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39447step1 raw39447step1Labels raw39447step2Labels labelEmbedding5 hl
    _ = mixedMoment B node4051 node4051Labels := by rfl

def raw39448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw39448Labels : Fin 3 → Fin 3 := ![1, 1, 2]

def raw39448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw39448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39448 raw39448Labels = mixedMoment B node4053 node4053Labels := by
  calc
    mixedMoment B raw39448 raw39448Labels = mixedMoment B raw39448step0 raw39448step0Labels := by
      have ha : raw39448step0 = raw39448 := by apply Matrix.ext; unfold raw39448step0 raw39448; decide +kernel
      have hl : raw39448Labels = labelEmbedding3 ∘ raw39448step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39448 raw39448Labels raw39448step0Labels labelEmbedding3 hl
    _ = mixedMoment B node4053 node4053Labels := by rfl

def raw39449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw39449Labels : Fin 3 → Fin 3 := ![2, 1, 2]

def raw39449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw39449step0Labels : Fin 3 → Fin 3 := ![2, 2, 1]

def raw39449step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw39449step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39449 raw39449Labels = mixedMoment B node4053 node4053Labels := by
  calc
    mixedMoment B raw39449 raw39449Labels = mixedMoment B raw39449step0 raw39449step0Labels := by
      have ha : raw39449step0 = (fun i j => raw39449 (permutation272 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39449step0 raw39449; decide +kernel
      have hl : raw39449step0Labels = raw39449Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39449 raw39449Labels permutation272 permutation3
    mixedMoment B raw39449step0 raw39449step0Labels = mixedMoment B raw39449step1 raw39449step1Labels := by
      have ha : raw39449step1 = raw39449step0 := by apply Matrix.ext; unfold raw39449step1 raw39449step0; decide +kernel
      have hl : raw39449step0Labels = labelEmbedding5 ∘ raw39449step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39449step0 raw39449step0Labels raw39449step1Labels labelEmbedding5 hl
    _ = mixedMoment B node4053 node4053Labels := by rfl

def raw39450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39450Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39450step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39450step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39450step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39450step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39450step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39450step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 3, 0], ![3, -3, 0]]
def raw39450step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39450step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw39450step4Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical39450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39450 raw39450Labels = mixedMoment B node2 node2Labels := by
  calc
    mixedMoment B raw39450 raw39450Labels = mixedMoment B raw39450step0 raw39450step0Labels := by
      have hz : ∀ j, raw39450 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39450step0 = (fun i j => raw39450 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39450step0 raw39450; decide +kernel
      have hl : raw39450step0Labels = raw39450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39450 raw39450Labels permutation520 hz
    mixedMoment B raw39450step0 raw39450step0Labels = mixedMoment B raw39450step1 raw39450step1Labels := by
      have hz : ∀ j, raw39450step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39450step1 = (fun i j => raw39450step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39450step1 raw39450step0; decide +kernel
      have hl : raw39450step1Labels = raw39450step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39450step0 raw39450step0Labels permutation104 hz
    mixedMoment B raw39450step1 raw39450step1Labels = mixedMoment B raw39450step2 raw39450step2Labels := by
      have hz : ∀ j, raw39450step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39450step2 = (fun i j => raw39450step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39450step2 raw39450step1; decide +kernel
      have hl : raw39450step2Labels = raw39450step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39450step1 raw39450step1Labels permutation20 hz
    mixedMoment B raw39450step2 raw39450step2Labels = mixedMoment B raw39450step3 raw39450step3Labels := by
      have hz : ∀ j, raw39450step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw39450step3 = (fun i j => raw39450step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw39450step3 raw39450step2; decide +kernel
      have hl : raw39450step3Labels = raw39450step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39450step2 raw39450step2Labels permutation4 hz
    mixedMoment B raw39450step3 raw39450step3Labels = mixedMoment B raw39450step4 raw39450step4Labels := by
      have hz : ∀ i, raw39450step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw39450step4 = (fun i j => raw39450step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw39450step4 raw39450step3; decide +kernel
      have hl : raw39450step4Labels = (fun j => raw39450step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw39450step3 raw39450step3Labels permutation6 hz
    _ = mixedMoment B node2 node2Labels := by rfl

def raw39451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39451Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39451step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39451step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39451step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39451step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39451step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39451step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw39451step3Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical39451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39451 raw39451Labels = mixedMoment B node1 node1Labels := by
  calc
    mixedMoment B raw39451 raw39451Labels = mixedMoment B raw39451step0 raw39451step0Labels := by
      have hz : ∀ j, raw39451 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39451step0 = (fun i j => raw39451 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39451step0 raw39451; decide +kernel
      have hl : raw39451step0Labels = raw39451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39451 raw39451Labels permutation434 hz
    mixedMoment B raw39451step0 raw39451step0Labels = mixedMoment B raw39451step1 raw39451step1Labels := by
      have hz : ∀ j, raw39451step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39451step1 = (fun i j => raw39451step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39451step1 raw39451step0; decide +kernel
      have hl : raw39451step1Labels = raw39451step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39451step0 raw39451step0Labels permutation80 hz
    mixedMoment B raw39451step1 raw39451step1Labels = mixedMoment B raw39451step2 raw39451step2Labels := by
      have hz : ∀ j, raw39451step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39451step2 = (fun i j => raw39451step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39451step2 raw39451step1; decide +kernel
      have hl : raw39451step2Labels = raw39451step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39451step1 raw39451step1Labels permutation14 hz
    mixedMoment B raw39451step2 raw39451step2Labels = mixedMoment B raw39451step3 raw39451step3Labels := by
      have hz : ∀ i, raw39451step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw39451step3 = (fun i j => raw39451step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw39451step3 raw39451step2; decide +kernel
      have hl : raw39451step3Labels = (fun j => raw39451step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw39451step2 raw39451step2Labels permutation6 hz
    _ = mixedMoment B node1 node1Labels := by rfl

def raw39452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39452Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39452step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39452step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39452step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39452step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39452step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw39452step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39452 raw39452Labels = mixedMoment B node272 node272Labels := by
  calc
    mixedMoment B raw39452 raw39452Labels = mixedMoment B raw39452step0 raw39452step0Labels := by
      have hz : ∀ j, raw39452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39452step0 = (fun i j => raw39452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39452step0 raw39452; decide +kernel
      have hl : raw39452step0Labels = raw39452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39452 raw39452Labels permutation434 hz
    mixedMoment B raw39452step0 raw39452step0Labels = mixedMoment B raw39452step1 raw39452step1Labels := by
      have hz : ∀ j, raw39452step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39452step1 = (fun i j => raw39452step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39452step1 raw39452step0; decide +kernel
      have hl : raw39452step1Labels = raw39452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39452step0 raw39452step0Labels permutation80 hz
    mixedMoment B raw39452step1 raw39452step1Labels = mixedMoment B raw39452step2 raw39452step2Labels := by
      have hz : ∀ j, raw39452step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39452step2 = (fun i j => raw39452step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39452step2 raw39452step1; decide +kernel
      have hl : raw39452step2Labels = raw39452step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39452step1 raw39452step1Labels permutation14 hz
    mixedMoment B raw39452step2 raw39452step2Labels = mixedMoment B raw39452step3 raw39452step3Labels := by
      have ha : raw39452step3 = (fun i j => raw39452step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39452step3 raw39452step2; decide +kernel
      have hl : raw39452step3Labels = raw39452step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39452step2 raw39452step2Labels permutation2 permutation3
    _ = mixedMoment B node272 node272Labels := by rfl

def raw39453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39453Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39453step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39453step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39453step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39453step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39453step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39453step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw39453step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39453step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw39453step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39453 raw39453Labels = mixedMoment B node270 node270Labels := by
  calc
    mixedMoment B raw39453 raw39453Labels = mixedMoment B raw39453step0 raw39453step0Labels := by
      have hz : ∀ j, raw39453 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39453step0 = (fun i j => raw39453 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39453step0 raw39453; decide +kernel
      have hl : raw39453step0Labels = raw39453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39453 raw39453Labels permutation434 hz
    mixedMoment B raw39453step0 raw39453step0Labels = mixedMoment B raw39453step1 raw39453step1Labels := by
      have hz : ∀ j, raw39453step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39453step1 = (fun i j => raw39453step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39453step1 raw39453step0; decide +kernel
      have hl : raw39453step1Labels = raw39453step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39453step0 raw39453step0Labels permutation80 hz
    mixedMoment B raw39453step1 raw39453step1Labels = mixedMoment B raw39453step2 raw39453step2Labels := by
      have hz : ∀ j, raw39453step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39453step2 = (fun i j => raw39453step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39453step2 raw39453step1; decide +kernel
      have hl : raw39453step2Labels = raw39453step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39453step1 raw39453step1Labels permutation14 hz
    mixedMoment B raw39453step2 raw39453step2Labels = mixedMoment B raw39453step3 raw39453step3Labels := by
      have ha : raw39453step3 = (fun i j => raw39453step2 (permutation3 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39453step3 raw39453step2; decide +kernel
      have hl : raw39453step3Labels = raw39453step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39453step2 raw39453step2Labels permutation3 permutation5
    mixedMoment B raw39453step3 raw39453step3Labels = mixedMoment B raw39453step4 raw39453step4Labels := by
      have ha : raw39453step4 = -raw39453step3 := by apply Matrix.ext; change ∀ i j, raw39453step4 i j = -(raw39453step3 i j); unfold raw39453step4 raw39453step3; decide +kernel
      have hl : raw39453step4Labels = raw39453step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node270 node270Labels := by rfl

def raw39454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39454Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39454step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39454step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39454step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39454step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39454 raw39454Labels = mixedMoment B node266 node266Labels := by
  calc
    mixedMoment B raw39454 raw39454Labels = mixedMoment B raw39454step0 raw39454step0Labels := by
      have hz : ∀ j, raw39454 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39454step0 = (fun i j => raw39454 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39454step0 raw39454; decide +kernel
      have hl : raw39454step0Labels = raw39454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39454 raw39454Labels permutation346 hz
    mixedMoment B raw39454step0 raw39454step0Labels = mixedMoment B raw39454step1 raw39454step1Labels := by
      have hz : ∀ j, raw39454step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39454step1 = (fun i j => raw39454step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39454step1 raw39454step0; decide +kernel
      have hl : raw39454step1Labels = raw39454step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39454step0 raw39454step0Labels permutation56 hz
    mixedMoment B raw39454step1 raw39454step1Labels = mixedMoment B raw39454step2 raw39454step2Labels := by
      have ha : raw39454step2 = (fun i j => raw39454step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39454step2 raw39454step1; decide +kernel
      have hl : raw39454step2Labels = raw39454step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39454step1 raw39454step1Labels permutation8 permutation3
    _ = mixedMoment B node266 node266Labels := by rfl

def raw39455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39455Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39455step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39455step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39455step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39455step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39455 raw39455Labels = mixedMoment B node267 node267Labels := by
  calc
    mixedMoment B raw39455 raw39455Labels = mixedMoment B raw39455step0 raw39455step0Labels := by
      have hz : ∀ j, raw39455 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39455step0 = (fun i j => raw39455 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39455step0 raw39455; decide +kernel
      have hl : raw39455step0Labels = raw39455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39455 raw39455Labels permutation346 hz
    mixedMoment B raw39455step0 raw39455step0Labels = mixedMoment B raw39455step1 raw39455step1Labels := by
      have hz : ∀ j, raw39455step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39455step1 = (fun i j => raw39455step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39455step1 raw39455step0; decide +kernel
      have hl : raw39455step1Labels = raw39455step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39455step0 raw39455step0Labels permutation56 hz
    mixedMoment B raw39455step1 raw39455step1Labels = mixedMoment B raw39455step2 raw39455step2Labels := by
      have ha : raw39455step2 = (fun i j => raw39455step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39455step2 raw39455step1; decide +kernel
      have hl : raw39455step2Labels = raw39455step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39455step1 raw39455step1Labels permutation8 permutation3
    _ = mixedMoment B node267 node267Labels := by rfl

def raw39456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39456Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39456step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39456step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39456step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39456step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39456step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39456 raw39456Labels = mixedMoment B node268 node268Labels := by
  calc
    mixedMoment B raw39456 raw39456Labels = mixedMoment B raw39456step0 raw39456step0Labels := by
      have hz : ∀ j, raw39456 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39456step0 = (fun i j => raw39456 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39456step0 raw39456; decide +kernel
      have hl : raw39456step0Labels = raw39456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39456 raw39456Labels permutation346 hz
    mixedMoment B raw39456step0 raw39456step0Labels = mixedMoment B raw39456step1 raw39456step1Labels := by
      have hz : ∀ j, raw39456step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39456step1 = (fun i j => raw39456step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39456step1 raw39456step0; decide +kernel
      have hl : raw39456step1Labels = raw39456step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39456step0 raw39456step0Labels permutation56 hz
    mixedMoment B raw39456step1 raw39456step1Labels = mixedMoment B raw39456step2 raw39456step2Labels := by
      have ha : raw39456step2 = (fun i j => raw39456step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39456step2 raw39456step1; decide +kernel
      have hl : raw39456step2Labels = raw39456step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39456step1 raw39456step1Labels permutation8 permutation3
    _ = mixedMoment B node268 node268Labels := by rfl

def raw39457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39457Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39457step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39457step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39457step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39457step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39457step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39457 raw39457Labels = mixedMoment B node269 node269Labels := by
  calc
    mixedMoment B raw39457 raw39457Labels = mixedMoment B raw39457step0 raw39457step0Labels := by
      have hz : ∀ j, raw39457 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39457step0 = (fun i j => raw39457 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39457step0 raw39457; decide +kernel
      have hl : raw39457step0Labels = raw39457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39457 raw39457Labels permutation346 hz
    mixedMoment B raw39457step0 raw39457step0Labels = mixedMoment B raw39457step1 raw39457step1Labels := by
      have hz : ∀ j, raw39457step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39457step1 = (fun i j => raw39457step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39457step1 raw39457step0; decide +kernel
      have hl : raw39457step1Labels = raw39457step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39457step0 raw39457step0Labels permutation56 hz
    mixedMoment B raw39457step1 raw39457step1Labels = mixedMoment B raw39457step2 raw39457step2Labels := by
      have ha : raw39457step2 = (fun i j => raw39457step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39457step2 raw39457step1; decide +kernel
      have hl : raw39457step2Labels = raw39457step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39457step1 raw39457step1Labels permutation8 permutation3
    _ = mixedMoment B node269 node269Labels := by rfl

def raw39458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39458Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39458step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39458step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39458step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39458step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39458step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39458step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39458step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39458 raw39458Labels = mixedMoment B node267 node267Labels := by
  calc
    mixedMoment B raw39458 raw39458Labels = mixedMoment B raw39458step0 raw39458step0Labels := by
      have hz : ∀ j, raw39458 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39458step0 = (fun i j => raw39458 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39458step0 raw39458; decide +kernel
      have hl : raw39458step0Labels = raw39458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39458 raw39458Labels permutation346 hz
    mixedMoment B raw39458step0 raw39458step0Labels = mixedMoment B raw39458step1 raw39458step1Labels := by
      have hz : ∀ j, raw39458step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39458step1 = (fun i j => raw39458step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39458step1 raw39458step0; decide +kernel
      have hl : raw39458step1Labels = raw39458step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39458step0 raw39458step0Labels permutation56 hz
    mixedMoment B raw39458step1 raw39458step1Labels = mixedMoment B raw39458step2 raw39458step2Labels := by
      have ha : raw39458step2 = (fun i j => raw39458step1 (permutation8 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39458step2 raw39458step1; decide +kernel
      have hl : raw39458step2Labels = raw39458step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39458step1 raw39458step1Labels permutation8 permutation5
    mixedMoment B raw39458step2 raw39458step2Labels = mixedMoment B raw39458step3 raw39458step3Labels := by
      have ha : raw39458step3 = -raw39458step2 := by apply Matrix.ext; change ∀ i j, raw39458step3 i j = -(raw39458step2 i j); unfold raw39458step3 raw39458step2; decide +kernel
      have hl : raw39458step3Labels = raw39458step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node267 node267Labels := by rfl

def raw39459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39459Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39459step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39459step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39459step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39459step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw39459step2Labels : Fin 2 → Fin 1 := ![0, 0]

theorem canonical39459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39459 raw39459Labels = mixedMoment B node0 node0Labels := by
  calc
    mixedMoment B raw39459 raw39459Labels = mixedMoment B raw39459step0 raw39459step0Labels := by
      have hz : ∀ j, raw39459 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39459step0 = (fun i j => raw39459 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39459step0 raw39459; decide +kernel
      have hl : raw39459step0Labels = raw39459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39459 raw39459Labels permutation346 hz
    mixedMoment B raw39459step0 raw39459step0Labels = mixedMoment B raw39459step1 raw39459step1Labels := by
      have hz : ∀ j, raw39459step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39459step1 = (fun i j => raw39459step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39459step1 raw39459step0; decide +kernel
      have hl : raw39459step1Labels = raw39459step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39459step0 raw39459step0Labels permutation56 hz
    mixedMoment B raw39459step1 raw39459step1Labels = mixedMoment B raw39459step2 raw39459step2Labels := by
      have hz : ∀ i, raw39459step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw39459step2 = (fun i j => raw39459step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw39459step2 raw39459step1; decide +kernel
      have hl : raw39459step2Labels = (fun j => raw39459step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw39459step1 raw39459step1Labels permutation6 hz
    _ = mixedMoment B node0 node0Labels := by rfl

def raw39460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39460Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39460step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39460step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39460 raw39460Labels = mixedMoment B node261 node261Labels := by
  calc
    mixedMoment B raw39460 raw39460Labels = mixedMoment B raw39460step0 raw39460step0Labels := by
      have hz : ∀ j, raw39460 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39460step0 = (fun i j => raw39460 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39460step0 raw39460; decide +kernel
      have hl : raw39460step0Labels = raw39460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39460 raw39460Labels permutation265 hz
    mixedMoment B raw39460step0 raw39460step0Labels = mixedMoment B raw39460step1 raw39460step1Labels := by
      have ha : raw39460step1 = (fun i j => raw39460step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39460step1 raw39460step0; decide +kernel
      have hl : raw39460step1Labels = raw39460step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39460step0 raw39460step0Labels permutation32 permutation3
    _ = mixedMoment B node261 node261Labels := by rfl

def raw39461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39461Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39461step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39461step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39461 raw39461Labels = mixedMoment B node265 node265Labels := by
  calc
    mixedMoment B raw39461 raw39461Labels = mixedMoment B raw39461step0 raw39461step0Labels := by
      have hz : ∀ j, raw39461 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39461step0 = (fun i j => raw39461 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39461step0 raw39461; decide +kernel
      have hl : raw39461step0Labels = raw39461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39461 raw39461Labels permutation265 hz
    mixedMoment B raw39461step0 raw39461step0Labels = mixedMoment B raw39461step1 raw39461step1Labels := by
      have ha : raw39461step1 = (fun i j => raw39461step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39461step1 raw39461step0; decide +kernel
      have hl : raw39461step1Labels = raw39461step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39461step0 raw39461step0Labels permutation32 permutation3
    _ = mixedMoment B node265 node265Labels := by rfl

def raw39462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw39462Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw39462step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39462step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39462step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39462step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39462 raw39462Labels = mixedMoment B node261 node261Labels := by
  calc
    mixedMoment B raw39462 raw39462Labels = mixedMoment B raw39462step0 raw39462step0Labels := by
      have hz : ∀ j, raw39462 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39462step0 = (fun i j => raw39462 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39462step0 raw39462; decide +kernel
      have hl : raw39462step0Labels = raw39462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39462 raw39462Labels permutation265 hz
    mixedMoment B raw39462step0 raw39462step0Labels = mixedMoment B raw39462step1 raw39462step1Labels := by
      have ha : raw39462step1 = (fun i j => raw39462step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39462step1 raw39462step0; decide +kernel
      have hl : raw39462step1Labels = raw39462step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39462step0 raw39462step0Labels permutation41 permutation5
    mixedMoment B raw39462step1 raw39462step1Labels = mixedMoment B raw39462step2 raw39462step2Labels := by
      have ha : raw39462step2 = -raw39462step1 := by apply Matrix.ext; change ∀ i j, raw39462step2 i j = -(raw39462step1 i j); unfold raw39462step2 raw39462step1; decide +kernel
      have hl : raw39462step2Labels = raw39462step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node261 node261Labels := by rfl

def raw39463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw39463Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39463step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39463 raw39463Labels = mixedMoment B node259 node259Labels := by
  calc
    mixedMoment B raw39463 raw39463Labels = mixedMoment B raw39463step0 raw39463step0Labels := by
      have ha : raw39463step0 = (fun i j => raw39463 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39463step0 raw39463; decide +kernel
      have hl : raw39463step0Labels = raw39463Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39463 raw39463Labels permutation152 permutation3
    _ = mixedMoment B node259 node259Labels := by rfl

def raw39464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39464Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39464step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39464step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw39464step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39464step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw39464step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39464step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw39464step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39464step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw39464step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39464 raw39464Labels = mixedMoment B node5502 node5502Labels := by
  calc
    mixedMoment B raw39464 raw39464Labels = mixedMoment B raw39464step0 raw39464step0Labels := by
      have hz : ∀ j, raw39464 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39464step0 = (fun i j => raw39464 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39464step0 raw39464; decide +kernel
      have hl : raw39464step0Labels = raw39464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39464 raw39464Labels permutation520 hz
    mixedMoment B raw39464step0 raw39464step0Labels = mixedMoment B raw39464step1 raw39464step1Labels := by
      have hz : ∀ j, raw39464step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39464step1 = (fun i j => raw39464step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39464step1 raw39464step0; decide +kernel
      have hl : raw39464step1Labels = raw39464step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39464step0 raw39464step0Labels permutation104 hz
    mixedMoment B raw39464step1 raw39464step1Labels = mixedMoment B raw39464step2 raw39464step2Labels := by
      have hz : ∀ j, raw39464step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39464step2 = (fun i j => raw39464step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39464step2 raw39464step1; decide +kernel
      have hl : raw39464step2Labels = raw39464step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39464step1 raw39464step1Labels permutation20 hz
    mixedMoment B raw39464step2 raw39464step2Labels = mixedMoment B raw39464step3 raw39464step3Labels := by
      have ha : raw39464step3 = (fun i j => raw39464step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39464step3 raw39464step2; decide +kernel
      have hl : raw39464step3Labels = raw39464step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39464step2 raw39464step2Labels permutation7 permutation3
    mixedMoment B raw39464step3 raw39464step3Labels = mixedMoment B raw39464step4 raw39464step4Labels := by
      have ha : raw39464step4 = -raw39464step3 := by apply Matrix.ext; change ∀ i j, raw39464step4 i j = -(raw39464step3 i j); unfold raw39464step4 raw39464step3; decide +kernel
      have hl : raw39464step4Labels = raw39464step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5502 node5502Labels := by rfl

def raw39465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw39465Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw39465step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39465step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw39465step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39465step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39465step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39465 raw39465Labels = mixedMoment B node388 node388Labels := by
  calc
    mixedMoment B raw39465 raw39465Labels = mixedMoment B raw39465step0 raw39465step0Labels := by
      have hz : ∀ j, raw39465 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39465step0 = (fun i j => raw39465 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39465step0 raw39465; decide +kernel
      have hl : raw39465step0Labels = raw39465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39465 raw39465Labels permutation434 hz
    mixedMoment B raw39465step0 raw39465step0Labels = mixedMoment B raw39465step1 raw39465step1Labels := by
      have hz : ∀ j, raw39465step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39465step1 = (fun i j => raw39465step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39465step1 raw39465step0; decide +kernel
      have hl : raw39465step1Labels = raw39465step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39465step0 raw39465step0Labels permutation80 hz
    mixedMoment B raw39465step1 raw39465step1Labels = mixedMoment B raw39465step2 raw39465step2Labels := by
      have ha : raw39465step2 = (fun i j => raw39465step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39465step2 raw39465step1; decide +kernel
      have hl : raw39465step2Labels = raw39465step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39465step1 raw39465step1Labels permutation8 permutation3
    _ = mixedMoment B node388 node388Labels := by rfl

def raw39466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39466Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39466step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39466step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw39466step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39466step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39466step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39466 raw39466Labels = mixedMoment B node389 node389Labels := by
  calc
    mixedMoment B raw39466 raw39466Labels = mixedMoment B raw39466step0 raw39466step0Labels := by
      have hz : ∀ j, raw39466 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39466step0 = (fun i j => raw39466 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39466step0 raw39466; decide +kernel
      have hl : raw39466step0Labels = raw39466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39466 raw39466Labels permutation434 hz
    mixedMoment B raw39466step0 raw39466step0Labels = mixedMoment B raw39466step1 raw39466step1Labels := by
      have hz : ∀ j, raw39466step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39466step1 = (fun i j => raw39466step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39466step1 raw39466step0; decide +kernel
      have hl : raw39466step1Labels = raw39466step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39466step0 raw39466step0Labels permutation80 hz
    mixedMoment B raw39466step1 raw39466step1Labels = mixedMoment B raw39466step2 raw39466step2Labels := by
      have ha : raw39466step2 = (fun i j => raw39466step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39466step2 raw39466step1; decide +kernel
      have hl : raw39466step2Labels = raw39466step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39466step1 raw39466step1Labels permutation8 permutation3
    _ = mixedMoment B node389 node389Labels := by rfl

def raw39467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39467Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39467step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39467step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw39467step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39467step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39467step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39467 raw39467Labels = mixedMoment B node391 node391Labels := by
  calc
    mixedMoment B raw39467 raw39467Labels = mixedMoment B raw39467step0 raw39467step0Labels := by
      have hz : ∀ j, raw39467 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39467step0 = (fun i j => raw39467 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39467step0 raw39467; decide +kernel
      have hl : raw39467step0Labels = raw39467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39467 raw39467Labels permutation434 hz
    mixedMoment B raw39467step0 raw39467step0Labels = mixedMoment B raw39467step1 raw39467step1Labels := by
      have hz : ∀ j, raw39467step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39467step1 = (fun i j => raw39467step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39467step1 raw39467step0; decide +kernel
      have hl : raw39467step1Labels = raw39467step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39467step0 raw39467step0Labels permutation80 hz
    mixedMoment B raw39467step1 raw39467step1Labels = mixedMoment B raw39467step2 raw39467step2Labels := by
      have ha : raw39467step2 = (fun i j => raw39467step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39467step2 raw39467step1; decide +kernel
      have hl : raw39467step2Labels = raw39467step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39467step1 raw39467step1Labels permutation8 permutation3
    _ = mixedMoment B node391 node391Labels := by rfl

def raw39468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39468Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39468step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39468step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39468 raw39468Labels = mixedMoment B node377 node377Labels := by
  calc
    mixedMoment B raw39468 raw39468Labels = mixedMoment B raw39468step0 raw39468step0Labels := by
      have hz : ∀ j, raw39468 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39468step0 = (fun i j => raw39468 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39468step0 raw39468; decide +kernel
      have hl : raw39468step0Labels = raw39468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39468 raw39468Labels permutation346 hz
    mixedMoment B raw39468step0 raw39468step0Labels = mixedMoment B raw39468step1 raw39468step1Labels := by
      have ha : raw39468step1 = (fun i j => raw39468step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39468step1 raw39468step0; decide +kernel
      have hl : raw39468step1Labels = raw39468step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39468step0 raw39468step0Labels permutation32 permutation3
    _ = mixedMoment B node377 node377Labels := by rfl

def raw39469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39469Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39469step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39469step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39469step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39469 raw39469Labels = mixedMoment B node384 node384Labels := by
  calc
    mixedMoment B raw39469 raw39469Labels = mixedMoment B raw39469step0 raw39469step0Labels := by
      have hz : ∀ j, raw39469 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39469step0 = (fun i j => raw39469 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39469step0 raw39469; decide +kernel
      have hl : raw39469step0Labels = raw39469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39469 raw39469Labels permutation346 hz
    mixedMoment B raw39469step0 raw39469step0Labels = mixedMoment B raw39469step1 raw39469step1Labels := by
      have ha : raw39469step1 = (fun i j => raw39469step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39469step1 raw39469step0; decide +kernel
      have hl : raw39469step1Labels = raw39469step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39469step0 raw39469step0Labels permutation32 permutation3
    _ = mixedMoment B node384 node384Labels := by rfl

def raw39470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw39470Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw39470step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw39470step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39470 raw39470Labels = mixedMoment B node386 node386Labels := by
  calc
    mixedMoment B raw39470 raw39470Labels = mixedMoment B raw39470step0 raw39470step0Labels := by
      have hz : ∀ j, raw39470 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39470step0 = (fun i j => raw39470 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39470step0 raw39470; decide +kernel
      have hl : raw39470step0Labels = raw39470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39470 raw39470Labels permutation346 hz
    mixedMoment B raw39470step0 raw39470step0Labels = mixedMoment B raw39470step1 raw39470step1Labels := by
      have ha : raw39470step1 = (fun i j => raw39470step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39470step1 raw39470step0; decide +kernel
      have hl : raw39470step1Labels = raw39470step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39470step0 raw39470step0Labels permutation32 permutation3
    _ = mixedMoment B node386 node386Labels := by rfl

def raw39471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39471Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39471step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39471step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39471 raw39471Labels = mixedMoment B node387 node387Labels := by
  calc
    mixedMoment B raw39471 raw39471Labels = mixedMoment B raw39471step0 raw39471step0Labels := by
      have hz : ∀ j, raw39471 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39471step0 = (fun i j => raw39471 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39471step0 raw39471; decide +kernel
      have hl : raw39471step0Labels = raw39471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39471 raw39471Labels permutation346 hz
    mixedMoment B raw39471step0 raw39471step0Labels = mixedMoment B raw39471step1 raw39471step1Labels := by
      have ha : raw39471step1 = (fun i j => raw39471step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39471step1 raw39471step0; decide +kernel
      have hl : raw39471step1Labels = raw39471step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39471step0 raw39471step0Labels permutation32 permutation3
    _ = mixedMoment B node387 node387Labels := by rfl

def raw39472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39472Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw39472step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39472 raw39472Labels = mixedMoment B node375 node375Labels := by
  calc
    mixedMoment B raw39472 raw39472Labels = mixedMoment B raw39472step0 raw39472step0Labels := by
      have ha : raw39472step0 = (fun i j => raw39472 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39472step0 raw39472; decide +kernel
      have hl : raw39472step0Labels = raw39472Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39472 raw39472Labels permutation152 permutation3
    _ = mixedMoment B node375 node375Labels := by rfl

def raw39473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw39473Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39473step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39473 raw39473Labels = mixedMoment B node382 node382Labels := by
  calc
    mixedMoment B raw39473 raw39473Labels = mixedMoment B raw39473step0 raw39473step0Labels := by
      have ha : raw39473step0 = (fun i j => raw39473 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39473step0 raw39473; decide +kernel
      have hl : raw39473step0Labels = raw39473Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39473 raw39473Labels permutation152 permutation3
    _ = mixedMoment B node382 node382Labels := by rfl

def raw39474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw39474Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw39474step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39474step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw39474step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39474step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![2, -3, 1]]
def raw39474step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39474step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw39474step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39474 raw39474Labels = mixedMoment B node415 node415Labels := by
  calc
    mixedMoment B raw39474 raw39474Labels = mixedMoment B raw39474step0 raw39474step0Labels := by
      have hz : ∀ j, raw39474 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39474step0 = (fun i j => raw39474 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39474step0 raw39474; decide +kernel
      have hl : raw39474step0Labels = raw39474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39474 raw39474Labels permutation434 hz
    mixedMoment B raw39474step0 raw39474step0Labels = mixedMoment B raw39474step1 raw39474step1Labels := by
      have hz : ∀ j, raw39474step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39474step1 = (fun i j => raw39474step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39474step1 raw39474step0; decide +kernel
      have hl : raw39474step1Labels = raw39474step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39474step0 raw39474step0Labels permutation80 hz
    mixedMoment B raw39474step1 raw39474step1Labels = mixedMoment B raw39474step2 raw39474step2Labels := by
      have hz : ∀ j, raw39474step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39474step2 = (fun i j => raw39474step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39474step2 raw39474step1; decide +kernel
      have hl : raw39474step2Labels = raw39474step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39474step1 raw39474step1Labels permutation14 hz
    mixedMoment B raw39474step2 raw39474step2Labels = mixedMoment B raw39474step3 raw39474step3Labels := by
      have ha : raw39474step3 = (fun i j => raw39474step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39474step3 raw39474step2; decide +kernel
      have hl : raw39474step3Labels = raw39474step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39474step2 raw39474step2Labels permutation2 permutation3
    _ = mixedMoment B node415 node415Labels := by rfl

def raw39475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39475Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39475step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39475step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39475step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39475step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39475step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39475step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw39475step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39475 raw39475Labels = mixedMoment B node419 node419Labels := by
  calc
    mixedMoment B raw39475 raw39475Labels = mixedMoment B raw39475step0 raw39475step0Labels := by
      have hz : ∀ j, raw39475 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39475step0 = (fun i j => raw39475 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39475step0 raw39475; decide +kernel
      have hl : raw39475step0Labels = raw39475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39475 raw39475Labels permutation434 hz
    mixedMoment B raw39475step0 raw39475step0Labels = mixedMoment B raw39475step1 raw39475step1Labels := by
      have hz : ∀ j, raw39475step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39475step1 = (fun i j => raw39475step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39475step1 raw39475step0; decide +kernel
      have hl : raw39475step1Labels = raw39475step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39475step0 raw39475step0Labels permutation80 hz
    mixedMoment B raw39475step1 raw39475step1Labels = mixedMoment B raw39475step2 raw39475step2Labels := by
      have hz : ∀ j, raw39475step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39475step2 = (fun i j => raw39475step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39475step2 raw39475step1; decide +kernel
      have hl : raw39475step2Labels = raw39475step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39475step1 raw39475step1Labels permutation14 hz
    mixedMoment B raw39475step2 raw39475step2Labels = mixedMoment B raw39475step3 raw39475step3Labels := by
      have ha : raw39475step3 = (fun i j => raw39475step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39475step3 raw39475step2; decide +kernel
      have hl : raw39475step3Labels = raw39475step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39475step2 raw39475step2Labels permutation2 permutation3
    _ = mixedMoment B node419 node419Labels := by rfl

def raw39476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39476Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39476step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39476step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39476step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39476step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39476step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39476step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw39476step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39476 raw39476Labels = mixedMoment B node420 node420Labels := by
  calc
    mixedMoment B raw39476 raw39476Labels = mixedMoment B raw39476step0 raw39476step0Labels := by
      have hz : ∀ j, raw39476 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39476step0 = (fun i j => raw39476 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39476step0 raw39476; decide +kernel
      have hl : raw39476step0Labels = raw39476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39476 raw39476Labels permutation434 hz
    mixedMoment B raw39476step0 raw39476step0Labels = mixedMoment B raw39476step1 raw39476step1Labels := by
      have hz : ∀ j, raw39476step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39476step1 = (fun i j => raw39476step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39476step1 raw39476step0; decide +kernel
      have hl : raw39476step1Labels = raw39476step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39476step0 raw39476step0Labels permutation80 hz
    mixedMoment B raw39476step1 raw39476step1Labels = mixedMoment B raw39476step2 raw39476step2Labels := by
      have hz : ∀ j, raw39476step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39476step2 = (fun i j => raw39476step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39476step2 raw39476step1; decide +kernel
      have hl : raw39476step2Labels = raw39476step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39476step1 raw39476step1Labels permutation14 hz
    mixedMoment B raw39476step2 raw39476step2Labels = mixedMoment B raw39476step3 raw39476step3Labels := by
      have ha : raw39476step3 = (fun i j => raw39476step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39476step3 raw39476step2; decide +kernel
      have hl : raw39476step3Labels = raw39476step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39476step2 raw39476step2Labels permutation2 permutation3
    _ = mixedMoment B node420 node420Labels := by rfl

def raw39477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw39477Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw39477step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39477step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw39477step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39477step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -3, 2], ![2, 1, -3]]
def raw39477step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39477step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw39477step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39477 raw39477Labels = mixedMoment B node421 node421Labels := by
  calc
    mixedMoment B raw39477 raw39477Labels = mixedMoment B raw39477step0 raw39477step0Labels := by
      have hz : ∀ j, raw39477 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39477step0 = (fun i j => raw39477 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39477step0 raw39477; decide +kernel
      have hl : raw39477step0Labels = raw39477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39477 raw39477Labels permutation434 hz
    mixedMoment B raw39477step0 raw39477step0Labels = mixedMoment B raw39477step1 raw39477step1Labels := by
      have hz : ∀ j, raw39477step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39477step1 = (fun i j => raw39477step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39477step1 raw39477step0; decide +kernel
      have hl : raw39477step1Labels = raw39477step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39477step0 raw39477step0Labels permutation80 hz
    mixedMoment B raw39477step1 raw39477step1Labels = mixedMoment B raw39477step2 raw39477step2Labels := by
      have hz : ∀ j, raw39477step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39477step2 = (fun i j => raw39477step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39477step2 raw39477step1; decide +kernel
      have hl : raw39477step2Labels = raw39477step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39477step1 raw39477step1Labels permutation14 hz
    mixedMoment B raw39477step2 raw39477step2Labels = mixedMoment B raw39477step3 raw39477step3Labels := by
      have ha : raw39477step3 = (fun i j => raw39477step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39477step3 raw39477step2; decide +kernel
      have hl : raw39477step3Labels = raw39477step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39477step2 raw39477step2Labels permutation2 permutation3
    _ = mixedMoment B node421 node421Labels := by rfl

def raw39478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw39478Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw39478step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw39478step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39478step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw39478step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39478 raw39478Labels = mixedMoment B node402 node402Labels := by
  calc
    mixedMoment B raw39478 raw39478Labels = mixedMoment B raw39478step0 raw39478step0Labels := by
      have hz : ∀ j, raw39478 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39478step0 = (fun i j => raw39478 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39478step0 raw39478; decide +kernel
      have hl : raw39478step0Labels = raw39478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39478 raw39478Labels permutation346 hz
    mixedMoment B raw39478step0 raw39478step0Labels = mixedMoment B raw39478step1 raw39478step1Labels := by
      have hz : ∀ j, raw39478step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39478step1 = (fun i j => raw39478step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39478step1 raw39478step0; decide +kernel
      have hl : raw39478step1Labels = raw39478step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39478step0 raw39478step0Labels permutation56 hz
    mixedMoment B raw39478step1 raw39478step1Labels = mixedMoment B raw39478step2 raw39478step2Labels := by
      have ha : raw39478step2 = (fun i j => raw39478step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39478step2 raw39478step1; decide +kernel
      have hl : raw39478step2Labels = raw39478step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39478step1 raw39478step1Labels permutation8 permutation3
    _ = mixedMoment B node402 node402Labels := by rfl

def raw39479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39479Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39479step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39479step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39479step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39479step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39479step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39479 raw39479Labels = mixedMoment B node405 node405Labels := by
  calc
    mixedMoment B raw39479 raw39479Labels = mixedMoment B raw39479step0 raw39479step0Labels := by
      have hz : ∀ j, raw39479 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39479step0 = (fun i j => raw39479 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39479step0 raw39479; decide +kernel
      have hl : raw39479step0Labels = raw39479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39479 raw39479Labels permutation346 hz
    mixedMoment B raw39479step0 raw39479step0Labels = mixedMoment B raw39479step1 raw39479step1Labels := by
      have hz : ∀ j, raw39479step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39479step1 = (fun i j => raw39479step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39479step1 raw39479step0; decide +kernel
      have hl : raw39479step1Labels = raw39479step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39479step0 raw39479step0Labels permutation56 hz
    mixedMoment B raw39479step1 raw39479step1Labels = mixedMoment B raw39479step2 raw39479step2Labels := by
      have ha : raw39479step2 = (fun i j => raw39479step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39479step2 raw39479step1; decide +kernel
      have hl : raw39479step2Labels = raw39479step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39479step1 raw39479step1Labels permutation8 permutation3
    _ = mixedMoment B node405 node405Labels := by rfl

def raw39480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39480Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39480step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39480step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39480step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39480step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39480step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39480step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39480 raw39480Labels = mixedMoment B node391 node391Labels := by
  calc
    mixedMoment B raw39480 raw39480Labels = mixedMoment B raw39480step0 raw39480step0Labels := by
      have hz : ∀ j, raw39480 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39480step0 = (fun i j => raw39480 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39480step0 raw39480; decide +kernel
      have hl : raw39480step0Labels = raw39480Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39480 raw39480Labels permutation346 hz
    mixedMoment B raw39480step0 raw39480step0Labels = mixedMoment B raw39480step1 raw39480step1Labels := by
      have hz : ∀ j, raw39480step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39480step1 = (fun i j => raw39480step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39480step1 raw39480step0; decide +kernel
      have hl : raw39480step1Labels = raw39480step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39480step0 raw39480step0Labels permutation56 hz
    mixedMoment B raw39480step1 raw39480step1Labels = mixedMoment B raw39480step2 raw39480step2Labels := by
      have ha : raw39480step2 = (fun i j => raw39480step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39480step2 raw39480step1; decide +kernel
      have hl : raw39480step2Labels = raw39480step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39480step1 raw39480step1Labels permutation30 permutation7
    _ = mixedMoment B node391 node391Labels := by rfl

def raw39481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw39481Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw39481step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39481step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw39481step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39481step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw39481step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39481 raw39481Labels = mixedMoment B node406 node406Labels := by
  calc
    mixedMoment B raw39481 raw39481Labels = mixedMoment B raw39481step0 raw39481step0Labels := by
      have hz : ∀ j, raw39481 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39481step0 = (fun i j => raw39481 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39481step0 raw39481; decide +kernel
      have hl : raw39481step0Labels = raw39481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39481 raw39481Labels permutation346 hz
    mixedMoment B raw39481step0 raw39481step0Labels = mixedMoment B raw39481step1 raw39481step1Labels := by
      have hz : ∀ j, raw39481step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39481step1 = (fun i j => raw39481step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39481step1 raw39481step0; decide +kernel
      have hl : raw39481step1Labels = raw39481step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39481step0 raw39481step0Labels permutation56 hz
    mixedMoment B raw39481step1 raw39481step1Labels = mixedMoment B raw39481step2 raw39481step2Labels := by
      have ha : raw39481step2 = (fun i j => raw39481step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39481step2 raw39481step1; decide +kernel
      have hl : raw39481step2Labels = raw39481step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39481step1 raw39481step1Labels permutation31 permutation4
    _ = mixedMoment B node406 node406Labels := by rfl

def raw39482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw39482Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw39482step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39482step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw39482step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39482step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw39482step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39482 raw39482Labels = mixedMoment B node414 node414Labels := by
  calc
    mixedMoment B raw39482 raw39482Labels = mixedMoment B raw39482step0 raw39482step0Labels := by
      have hz : ∀ j, raw39482 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39482step0 = (fun i j => raw39482 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39482step0 raw39482; decide +kernel
      have hl : raw39482step0Labels = raw39482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39482 raw39482Labels permutation346 hz
    mixedMoment B raw39482step0 raw39482step0Labels = mixedMoment B raw39482step1 raw39482step1Labels := by
      have hz : ∀ j, raw39482step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39482step1 = (fun i j => raw39482step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39482step1 raw39482step0; decide +kernel
      have hl : raw39482step1Labels = raw39482step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39482step0 raw39482step0Labels permutation56 hz
    mixedMoment B raw39482step1 raw39482step1Labels = mixedMoment B raw39482step2 raw39482step2Labels := by
      have ha : raw39482step2 = (fun i j => raw39482step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39482step2 raw39482step1; decide +kernel
      have hl : raw39482step2Labels = raw39482step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39482step1 raw39482step1Labels permutation8 permutation3
    _ = mixedMoment B node414 node414Labels := by rfl

def raw39483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39483Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw39483step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw39483step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39483 raw39483Labels = mixedMoment B node400 node400Labels := by
  calc
    mixedMoment B raw39483 raw39483Labels = mixedMoment B raw39483step0 raw39483step0Labels := by
      have hz : ∀ j, raw39483 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39483step0 = (fun i j => raw39483 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39483step0 raw39483; decide +kernel
      have hl : raw39483step0Labels = raw39483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39483 raw39483Labels permutation265 hz
    mixedMoment B raw39483step0 raw39483step0Labels = mixedMoment B raw39483step1 raw39483step1Labels := by
      have ha : raw39483step1 = (fun i j => raw39483step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39483step1 raw39483step0; decide +kernel
      have hl : raw39483step1Labels = raw39483step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39483step0 raw39483step0Labels permutation32 permutation3
    _ = mixedMoment B node400 node400Labels := by rfl

def raw39484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw39484Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw39484step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39484step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39484 raw39484Labels = mixedMoment B node409 node409Labels := by
  calc
    mixedMoment B raw39484 raw39484Labels = mixedMoment B raw39484step0 raw39484step0Labels := by
      have hz : ∀ j, raw39484 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39484step0 = (fun i j => raw39484 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39484step0 raw39484; decide +kernel
      have hl : raw39484step0Labels = raw39484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39484 raw39484Labels permutation265 hz
    mixedMoment B raw39484step0 raw39484step0Labels = mixedMoment B raw39484step1 raw39484step1Labels := by
      have ha : raw39484step1 = (fun i j => raw39484step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39484step1 raw39484step0; decide +kernel
      have hl : raw39484step1Labels = raw39484step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39484step0 raw39484step0Labels permutation32 permutation3
    _ = mixedMoment B node409 node409Labels := by rfl

def raw39485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39485Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39485step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39485step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw39485step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39485step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw39485step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39485step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw39485step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39485step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw39485step4Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39485 raw39485Labels = mixedMoment B node270 node270Labels := by
  calc
    mixedMoment B raw39485 raw39485Labels = mixedMoment B raw39485step0 raw39485step0Labels := by
      have hz : ∀ j, raw39485 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39485step0 = (fun i j => raw39485 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39485step0 raw39485; decide +kernel
      have hl : raw39485step0Labels = raw39485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39485 raw39485Labels permutation520 hz
    mixedMoment B raw39485step0 raw39485step0Labels = mixedMoment B raw39485step1 raw39485step1Labels := by
      have hz : ∀ j, raw39485step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39485step1 = (fun i j => raw39485step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39485step1 raw39485step0; decide +kernel
      have hl : raw39485step1Labels = raw39485step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39485step0 raw39485step0Labels permutation104 hz
    mixedMoment B raw39485step1 raw39485step1Labels = mixedMoment B raw39485step2 raw39485step2Labels := by
      have hz : ∀ j, raw39485step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39485step2 = (fun i j => raw39485step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39485step2 raw39485step1; decide +kernel
      have hl : raw39485step2Labels = raw39485step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39485step1 raw39485step1Labels permutation20 hz
    mixedMoment B raw39485step2 raw39485step2Labels = mixedMoment B raw39485step3 raw39485step3Labels := by
      have ha : raw39485step3 = (fun i j => raw39485step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39485step3 raw39485step2; decide +kernel
      have hl : raw39485step3Labels = raw39485step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39485step2 raw39485step2Labels permutation7 permutation3
    mixedMoment B raw39485step3 raw39485step3Labels = mixedMoment B raw39485step4 raw39485step4Labels := by
      have ha : raw39485step4 = -raw39485step3 := by apply Matrix.ext; change ∀ i j, raw39485step4 i j = -(raw39485step3 i j); unfold raw39485step4 raw39485step3; decide +kernel
      have hl : raw39485step4Labels = raw39485step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node270 node270Labels := by rfl

def raw39486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw39486Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39486step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw39486step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39486step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw39486step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39486step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw39486step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39486 raw39486Labels = mixedMoment B node391 node391Labels := by
  calc
    mixedMoment B raw39486 raw39486Labels = mixedMoment B raw39486step0 raw39486step0Labels := by
      have hz : ∀ j, raw39486 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39486step0 = (fun i j => raw39486 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39486step0 raw39486; decide +kernel
      have hl : raw39486step0Labels = raw39486Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39486 raw39486Labels permutation434 hz
    mixedMoment B raw39486step0 raw39486step0Labels = mixedMoment B raw39486step1 raw39486step1Labels := by
      have hz : ∀ j, raw39486step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39486step1 = (fun i j => raw39486step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39486step1 raw39486step0; decide +kernel
      have hl : raw39486step1Labels = raw39486step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39486step0 raw39486step0Labels permutation80 hz
    mixedMoment B raw39486step1 raw39486step1Labels = mixedMoment B raw39486step2 raw39486step2Labels := by
      have ha : raw39486step2 = (fun i j => raw39486step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39486step2 raw39486step1; decide +kernel
      have hl : raw39486step2Labels = raw39486step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39486step1 raw39486step1Labels permutation30 permutation5
    _ = mixedMoment B node391 node391Labels := by rfl

def raw39487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39487Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39487step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39487step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39487step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39487 raw39487Labels = mixedMoment B node412 node412Labels := by
  calc
    mixedMoment B raw39487 raw39487Labels = mixedMoment B raw39487step0 raw39487step0Labels := by
      have hz : ∀ j, raw39487 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39487step0 = (fun i j => raw39487 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39487step0 raw39487; decide +kernel
      have hl : raw39487step0Labels = raw39487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39487 raw39487Labels permutation434 hz
    mixedMoment B raw39487step0 raw39487step0Labels = mixedMoment B raw39487step1 raw39487step1Labels := by
      have hz : ∀ j, raw39487step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39487step1 = (fun i j => raw39487step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39487step1 raw39487step0; decide +kernel
      have hl : raw39487step1Labels = raw39487step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39487step0 raw39487step0Labels permutation80 hz
    _ = mixedMoment B node412 node412Labels := by rfl

def raw39488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39488Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39488step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39488step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw39488step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39488 raw39488Labels = mixedMoment B node410 node410Labels := by
  calc
    mixedMoment B raw39488 raw39488Labels = mixedMoment B raw39488step0 raw39488step0Labels := by
      have hz : ∀ j, raw39488 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39488step0 = (fun i j => raw39488 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39488step0 raw39488; decide +kernel
      have hl : raw39488step0Labels = raw39488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39488 raw39488Labels permutation434 hz
    mixedMoment B raw39488step0 raw39488step0Labels = mixedMoment B raw39488step1 raw39488step1Labels := by
      have hz : ∀ j, raw39488step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39488step1 = (fun i j => raw39488step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39488step1 raw39488step0; decide +kernel
      have hl : raw39488step1Labels = raw39488step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39488step0 raw39488step0Labels permutation80 hz
    _ = mixedMoment B node410 node410Labels := by rfl

def raw39489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39489Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39489step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39489step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw39489step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39489 raw39489Labels = mixedMoment B node408 node408Labels := by
  calc
    mixedMoment B raw39489 raw39489Labels = mixedMoment B raw39489step0 raw39489step0Labels := by
      have hz : ∀ j, raw39489 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39489step0 = (fun i j => raw39489 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39489step0 raw39489; decide +kernel
      have hl : raw39489step0Labels = raw39489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39489 raw39489Labels permutation434 hz
    mixedMoment B raw39489step0 raw39489step0Labels = mixedMoment B raw39489step1 raw39489step1Labels := by
      have hz : ∀ j, raw39489step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39489step1 = (fun i j => raw39489step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39489step1 raw39489step0; decide +kernel
      have hl : raw39489step1Labels = raw39489step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39489step0 raw39489step0Labels permutation80 hz
    _ = mixedMoment B node408 node408Labels := by rfl

def raw39490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39490Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39490step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39490step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39490step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw39490step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39490 raw39490Labels = mixedMoment B node384 node384Labels := by
  calc
    mixedMoment B raw39490 raw39490Labels = mixedMoment B raw39490step0 raw39490step0Labels := by
      have hz : ∀ j, raw39490 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39490step0 = (fun i j => raw39490 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39490step0 raw39490; decide +kernel
      have hl : raw39490step0Labels = raw39490Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39490 raw39490Labels permutation346 hz
    mixedMoment B raw39490step0 raw39490step0Labels = mixedMoment B raw39490step1 raw39490step1Labels := by
      have ha : raw39490step1 = (fun i j => raw39490step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39490step1 raw39490step0; decide +kernel
      have hl : raw39490step1Labels = raw39490step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39490step0 raw39490step0Labels permutation38 permutation2
    _ = mixedMoment B node384 node384Labels := by rfl

def raw39491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39491Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39491step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw39491step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39491 raw39491Labels = mixedMoment B node381 node381Labels := by
  calc
    mixedMoment B raw39491 raw39491Labels = mixedMoment B raw39491step0 raw39491step0Labels := by
      have hz : ∀ j, raw39491 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39491step0 = (fun i j => raw39491 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39491step0 raw39491; decide +kernel
      have hl : raw39491step0Labels = raw39491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39491 raw39491Labels permutation346 hz
    mixedMoment B raw39491step0 raw39491step0Labels = mixedMoment B raw39491step1 raw39491step1Labels := by
      have ha : raw39491step1 = (fun i j => raw39491step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39491step1 raw39491step0; decide +kernel
      have hl : raw39491step1Labels = raw39491step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39491step0 raw39491step0Labels permutation38 permutation2
    _ = mixedMoment B node381 node381Labels := by rfl

def raw39492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39492Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39492step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw39492step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39492 raw39492Labels = mixedMoment B node364 node364Labels := by
  calc
    mixedMoment B raw39492 raw39492Labels = mixedMoment B raw39492step0 raw39492step0Labels := by
      have hz : ∀ j, raw39492 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39492step0 = (fun i j => raw39492 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39492step0 raw39492; decide +kernel
      have hl : raw39492step0Labels = raw39492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39492 raw39492Labels permutation346 hz
    mixedMoment B raw39492step0 raw39492step0Labels = mixedMoment B raw39492step1 raw39492step1Labels := by
      have ha : raw39492step1 = (fun i j => raw39492step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39492step1 raw39492step0; decide +kernel
      have hl : raw39492step1Labels = raw39492step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39492step0 raw39492step0Labels permutation38 permutation2
    _ = mixedMoment B node364 node364Labels := by rfl

def raw39493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw39493Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw39493step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw39493step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39493 raw39493Labels = mixedMoment B node393 node393Labels := by
  calc
    mixedMoment B raw39493 raw39493Labels = mixedMoment B raw39493step0 raw39493step0Labels := by
      have hz : ∀ j, raw39493 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39493step0 = (fun i j => raw39493 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39493step0 raw39493; decide +kernel
      have hl : raw39493step0Labels = raw39493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39493 raw39493Labels permutation346 hz
    mixedMoment B raw39493step0 raw39493step0Labels = mixedMoment B raw39493step1 raw39493step1Labels := by
      have ha : raw39493step1 = (fun i j => raw39493step0 (permutation144 i) (permutation4 j)) := by apply Matrix.ext; unfold raw39493step1 raw39493step0; decide +kernel
      have hl : raw39493step1Labels = raw39493step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39493step0 raw39493step0Labels permutation144 permutation4
    _ = mixedMoment B node393 node393Labels := by rfl

def raw39494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39494Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39494step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39494step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39494 raw39494Labels = mixedMoment B node409 node409Labels := by
  calc
    mixedMoment B raw39494 raw39494Labels = mixedMoment B raw39494step0 raw39494step0Labels := by
      have hz : ∀ j, raw39494 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39494step0 = (fun i j => raw39494 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39494step0 raw39494; decide +kernel
      have hl : raw39494step0Labels = raw39494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39494 raw39494Labels permutation346 hz
    mixedMoment B raw39494step0 raw39494step0Labels = mixedMoment B raw39494step1 raw39494step1Labels := by
      have ha : raw39494step1 = (fun i j => raw39494step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39494step1 raw39494step0; decide +kernel
      have hl : raw39494step1Labels = raw39494step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39494step0 raw39494step0Labels permutation37 permutation2
    _ = mixedMoment B node409 node409Labels := by rfl

def raw39495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39495Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw39495step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39495 raw39495Labels = mixedMoment B node380 node380Labels := by
  calc
    mixedMoment B raw39495 raw39495Labels = mixedMoment B raw39495step0 raw39495step0Labels := by
      have ha : raw39495step0 = (fun i j => raw39495 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39495step0 raw39495; decide +kernel
      have hl : raw39495step0Labels = raw39495Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39495 raw39495Labels permutation180 permutation2
    _ = mixedMoment B node380 node380Labels := by rfl

def raw39496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw39496Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39496step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39496 raw39496Labels = mixedMoment B node363 node363Labels := by
  calc
    mixedMoment B raw39496 raw39496Labels = mixedMoment B raw39496step0 raw39496step0Labels := by
      have ha : raw39496step0 = (fun i j => raw39496 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39496step0 raw39496; decide +kernel
      have hl : raw39496step0Labels = raw39496Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39496 raw39496Labels permutation180 permutation2
    _ = mixedMoment B node363 node363Labels := by rfl

def raw39497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw39497Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw39497step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw39497step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39497 raw39497Labels = mixedMoment B node386 node386Labels := by
  calc
    mixedMoment B raw39497 raw39497Labels = mixedMoment B raw39497step0 raw39497step0Labels := by
      have hz : ∀ j, raw39497 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39497step0 = (fun i j => raw39497 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39497step0 raw39497; decide +kernel
      have hl : raw39497step0Labels = raw39497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39497 raw39497Labels permutation434 hz
    mixedMoment B raw39497step0 raw39497step0Labels = mixedMoment B raw39497step1 raw39497step1Labels := by
      have ha : raw39497step1 = (fun i j => raw39497step0 (permutation149 i) (permutation5 j)) := by apply Matrix.ext; unfold raw39497step1 raw39497step0; decide +kernel
      have hl : raw39497step1Labels = raw39497step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39497step0 raw39497step0Labels permutation149 permutation5
    _ = mixedMoment B node386 node386Labels := by rfl

def raw39498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39498Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw39498step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39498 raw39498Labels = mixedMoment B node397 node397Labels := by
  calc
    mixedMoment B raw39498 raw39498Labels = mixedMoment B raw39498step0 raw39498step0Labels := by
      have hz : ∀ j, raw39498 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39498step0 = (fun i j => raw39498 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39498step0 raw39498; decide +kernel
      have hl : raw39498step0Labels = raw39498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39498 raw39498Labels permutation434 hz
    _ = mixedMoment B node397 node397Labels := by rfl

def raw39499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39499Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw39499step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39499 raw39499Labels = mixedMoment B node393 node393Labels := by
  calc
    mixedMoment B raw39499 raw39499Labels = mixedMoment B raw39499step0 raw39499step0Labels := by
      have hz : ∀ j, raw39499 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39499step0 = (fun i j => raw39499 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39499step0 raw39499; decide +kernel
      have hl : raw39499step0Labels = raw39499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39499 raw39499Labels permutation434 hz
    _ = mixedMoment B node393 node393Labels := by rfl

def raw39500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39500Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39500step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39500 raw39500Labels = mixedMoment B node357 node357Labels := by
  calc
    mixedMoment B raw39500 raw39500Labels = mixedMoment B raw39500step0 raw39500step0Labels := by
      have ha : raw39500step0 = (fun i j => raw39500 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39500step0 raw39500; decide +kernel
      have hl : raw39500step0Labels = raw39500Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39500 raw39500Labels permutation200 permutation2
    _ = mixedMoment B node357 node357Labels := by rfl

def raw39501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw39501Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw39501step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39501 raw39501Labels = mixedMoment B node392 node392Labels := by
  calc
    mixedMoment B raw39501 raw39501Labels = mixedMoment B raw39501step0 raw39501step0Labels := by
      have ha : raw39501step0 = (fun i j => raw39501 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39501step0 raw39501; decide +kernel
      have hl : raw39501step0Labels = raw39501Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39501 raw39501Labels permutation156 permutation2
    _ = mixedMoment B node392 node392Labels := by rfl

def raw39502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39502Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw39502step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39502 raw39502Labels = mixedMoment B node394 node394Labels := by
  calc
    mixedMoment B raw39502 raw39502Labels = mixedMoment B raw39502step0 raw39502step0Labels := by
      have ha : raw39502step0 = (fun i j => raw39502 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39502step0 raw39502; decide +kernel
      have hl : raw39502step0Labels = raw39502Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39502 raw39502Labels permutation157 permutation2
    _ = mixedMoment B node394 node394Labels := by rfl

def raw39503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw39503Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw39503step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39503step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw39503step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39503 raw39503Labels = mixedMoment B node406 node406Labels := by
  calc
    mixedMoment B raw39503 raw39503Labels = mixedMoment B raw39503step0 raw39503step0Labels := by
      have hz : ∀ j, raw39503 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39503step0 = (fun i j => raw39503 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39503step0 raw39503; decide +kernel
      have hl : raw39503step0Labels = raw39503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39503 raw39503Labels permutation434 hz
    mixedMoment B raw39503step0 raw39503step0Labels = mixedMoment B raw39503step1 raw39503step1Labels := by
      have hz : ∀ j, raw39503step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39503step1 = (fun i j => raw39503step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39503step1 raw39503step0; decide +kernel
      have hl : raw39503step1Labels = raw39503step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39503step0 raw39503step0Labels permutation80 hz
    _ = mixedMoment B node406 node406Labels := by rfl

def raw39504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39504Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39504step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39504step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39504step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw39504step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39504 raw39504Labels = mixedMoment B node404 node404Labels := by
  calc
    mixedMoment B raw39504 raw39504Labels = mixedMoment B raw39504step0 raw39504step0Labels := by
      have hz : ∀ j, raw39504 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39504step0 = (fun i j => raw39504 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39504step0 raw39504; decide +kernel
      have hl : raw39504step0Labels = raw39504Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39504 raw39504Labels permutation434 hz
    mixedMoment B raw39504step0 raw39504step0Labels = mixedMoment B raw39504step1 raw39504step1Labels := by
      have hz : ∀ j, raw39504step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39504step1 = (fun i j => raw39504step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39504step1 raw39504step0; decide +kernel
      have hl : raw39504step1Labels = raw39504step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39504step0 raw39504step0Labels permutation80 hz
    _ = mixedMoment B node404 node404Labels := by rfl

def raw39505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw39505Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw39505step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw39505step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39505step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw39505step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39505 raw39505Labels = mixedMoment B node342 node342Labels := by
  calc
    mixedMoment B raw39505 raw39505Labels = mixedMoment B raw39505step0 raw39505step0Labels := by
      have hz : ∀ j, raw39505 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39505step0 = (fun i j => raw39505 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39505step0 raw39505; decide +kernel
      have hl : raw39505step0Labels = raw39505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39505 raw39505Labels permutation434 hz
    mixedMoment B raw39505step0 raw39505step0Labels = mixedMoment B raw39505step1 raw39505step1Labels := by
      have hz : ∀ j, raw39505step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39505step1 = (fun i j => raw39505step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39505step1 raw39505step0; decide +kernel
      have hl : raw39505step1Labels = raw39505step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39505step0 raw39505step0Labels permutation80 hz
    mixedMoment B raw39505step1 raw39505step1Labels = mixedMoment B raw39505step2 raw39505step2Labels := by
      have ha : raw39505step2 = (fun i j => raw39505step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39505step2 raw39505step1; decide +kernel
      have hl : raw39505step2Labels = raw39505step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39505step1 raw39505step1Labels permutation29 permutation7
    _ = mixedMoment B node342 node342Labels := by rfl

def raw39506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39506Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39506step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39506step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39506 raw39506Labels = mixedMoment B node377 node377Labels := by
  calc
    mixedMoment B raw39506 raw39506Labels = mixedMoment B raw39506step0 raw39506step0Labels := by
      have hz : ∀ j, raw39506 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39506step0 = (fun i j => raw39506 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39506step0 raw39506; decide +kernel
      have hl : raw39506step0Labels = raw39506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39506 raw39506Labels permutation346 hz
    mixedMoment B raw39506step0 raw39506step0Labels = mixedMoment B raw39506step1 raw39506step1Labels := by
      have ha : raw39506step1 = (fun i j => raw39506step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39506step1 raw39506step0; decide +kernel
      have hl : raw39506step1Labels = raw39506step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39506step0 raw39506step0Labels permutation38 permutation2
    _ = mixedMoment B node377 node377Labels := by rfl

def raw39507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39507Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw39507step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw39507step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39507 raw39507Labels = mixedMoment B node324 node324Labels := by
  calc
    mixedMoment B raw39507 raw39507Labels = mixedMoment B raw39507step0 raw39507step0Labels := by
      have hz : ∀ j, raw39507 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39507step0 = (fun i j => raw39507 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39507step0 raw39507; decide +kernel
      have hl : raw39507step0Labels = raw39507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39507 raw39507Labels permutation346 hz
    mixedMoment B raw39507step0 raw39507step0Labels = mixedMoment B raw39507step1 raw39507step1Labels := by
      have ha : raw39507step1 = (fun i j => raw39507step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39507step1 raw39507step0; decide +kernel
      have hl : raw39507step1Labels = raw39507step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39507step0 raw39507step0Labels permutation139 permutation7
    _ = mixedMoment B node324 node324Labels := by rfl

def raw39508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw39508Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw39508step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw39508step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39508 raw39508Labels = mixedMoment B node399 node399Labels := by
  calc
    mixedMoment B raw39508 raw39508Labels = mixedMoment B raw39508step0 raw39508step0Labels := by
      have hz : ∀ j, raw39508 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39508step0 = (fun i j => raw39508 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39508step0 raw39508; decide +kernel
      have hl : raw39508step0Labels = raw39508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39508 raw39508Labels permutation346 hz
    mixedMoment B raw39508step0 raw39508step0Labels = mixedMoment B raw39508step1 raw39508step1Labels := by
      have ha : raw39508step1 = (fun i j => raw39508step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39508step1 raw39508step0; decide +kernel
      have hl : raw39508step1Labels = raw39508step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39508step0 raw39508step0Labels permutation37 permutation2
    _ = mixedMoment B node399 node399Labels := by rfl

def raw39509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw39509Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw39509step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw39509step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39509 raw39509Labels = mixedMoment B node400 node400Labels := by
  calc
    mixedMoment B raw39509 raw39509Labels = mixedMoment B raw39509step0 raw39509step0Labels := by
      have hz : ∀ j, raw39509 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39509step0 = (fun i j => raw39509 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39509step0 raw39509; decide +kernel
      have hl : raw39509step0Labels = raw39509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39509 raw39509Labels permutation346 hz
    mixedMoment B raw39509step0 raw39509step0Labels = mixedMoment B raw39509step1 raw39509step1Labels := by
      have ha : raw39509step1 = (fun i j => raw39509step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39509step1 raw39509step0; decide +kernel
      have hl : raw39509step1Labels = raw39509step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39509step0 raw39509step0Labels permutation37 permutation2
    _ = mixedMoment B node400 node400Labels := by rfl

def raw39510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39510Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39510step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw39510step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39510 raw39510Labels = mixedMoment B node403 node403Labels := by
  calc
    mixedMoment B raw39510 raw39510Labels = mixedMoment B raw39510step0 raw39510step0Labels := by
      have hz : ∀ j, raw39510 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39510step0 = (fun i j => raw39510 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39510step0 raw39510; decide +kernel
      have hl : raw39510step0Labels = raw39510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39510 raw39510Labels permutation346 hz
    mixedMoment B raw39510step0 raw39510step0Labels = mixedMoment B raw39510step1 raw39510step1Labels := by
      have ha : raw39510step1 = (fun i j => raw39510step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39510step1 raw39510step0; decide +kernel
      have hl : raw39510step1Labels = raw39510step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39510step0 raw39510step0Labels permutation35 permutation2
    _ = mixedMoment B node403 node403Labels := by rfl

def raw39511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw39511Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39511step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39511 raw39511Labels = mixedMoment B node376 node376Labels := by
  calc
    mixedMoment B raw39511 raw39511Labels = mixedMoment B raw39511step0 raw39511step0Labels := by
      have ha : raw39511step0 = (fun i j => raw39511 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39511step0 raw39511; decide +kernel
      have hl : raw39511step0Labels = raw39511Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39511 raw39511Labels permutation180 permutation2
    _ = mixedMoment B node376 node376Labels := by rfl

def raw39512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw39512Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39512step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39512 raw39512Labels = mixedMoment B node359 node359Labels := by
  calc
    mixedMoment B raw39512 raw39512Labels = mixedMoment B raw39512step0 raw39512step0Labels := by
      have ha : raw39512step0 = (fun i j => raw39512 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39512step0 raw39512; decide +kernel
      have hl : raw39512step0Labels = raw39512Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39512 raw39512Labels permutation181 permutation2
    _ = mixedMoment B node359 node359Labels := by rfl

def raw39513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw39513Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw39513step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39513step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw39513step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39513step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![2, -3, 1]]
def raw39513step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39513 raw39513Labels = mixedMoment B node421 node421Labels := by
  calc
    mixedMoment B raw39513 raw39513Labels = mixedMoment B raw39513step0 raw39513step0Labels := by
      have hz : ∀ j, raw39513 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39513step0 = (fun i j => raw39513 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39513step0 raw39513; decide +kernel
      have hl : raw39513step0Labels = raw39513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39513 raw39513Labels permutation434 hz
    mixedMoment B raw39513step0 raw39513step0Labels = mixedMoment B raw39513step1 raw39513step1Labels := by
      have hz : ∀ j, raw39513step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39513step1 = (fun i j => raw39513step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39513step1 raw39513step0; decide +kernel
      have hl : raw39513step1Labels = raw39513step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39513step0 raw39513step0Labels permutation80 hz
    mixedMoment B raw39513step1 raw39513step1Labels = mixedMoment B raw39513step2 raw39513step2Labels := by
      have hz : ∀ j, raw39513step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39513step2 = (fun i j => raw39513step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39513step2 raw39513step1; decide +kernel
      have hl : raw39513step2Labels = raw39513step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39513step1 raw39513step1Labels permutation14 hz
    _ = mixedMoment B node421 node421Labels := by rfl

def raw39514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw39514Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw39514step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39514step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw39514step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39514step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![2, 2, -4]]
def raw39514step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39514step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -3, 1], ![2, 1, -3]]
def raw39514step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39514 raw39514Labels = mixedMoment B node159 node159Labels := by
  calc
    mixedMoment B raw39514 raw39514Labels = mixedMoment B raw39514step0 raw39514step0Labels := by
      have hz : ∀ j, raw39514 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39514step0 = (fun i j => raw39514 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39514step0 raw39514; decide +kernel
      have hl : raw39514step0Labels = raw39514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39514 raw39514Labels permutation434 hz
    mixedMoment B raw39514step0 raw39514step0Labels = mixedMoment B raw39514step1 raw39514step1Labels := by
      have hz : ∀ j, raw39514step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39514step1 = (fun i j => raw39514step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39514step1 raw39514step0; decide +kernel
      have hl : raw39514step1Labels = raw39514step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39514step0 raw39514step0Labels permutation80 hz
    mixedMoment B raw39514step1 raw39514step1Labels = mixedMoment B raw39514step2 raw39514step2Labels := by
      have hz : ∀ j, raw39514step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw39514step2 = (fun i j => raw39514step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw39514step2 raw39514step1; decide +kernel
      have hl : raw39514step2Labels = raw39514step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39514step1 raw39514step1Labels permutation14 hz
    mixedMoment B raw39514step2 raw39514step2Labels = mixedMoment B raw39514step3 raw39514step3Labels := by
      have ha : raw39514step3 = (fun i j => raw39514step2 (permutation6 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39514step3 raw39514step2; decide +kernel
      have hl : raw39514step3Labels = raw39514step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39514step2 raw39514step2Labels permutation6 permutation6
    _ = mixedMoment B node159 node159Labels := by rfl

def raw39515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39515Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39515step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39515step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw39515step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39515 raw39515Labels = mixedMoment B node388 node388Labels := by
  calc
    mixedMoment B raw39515 raw39515Labels = mixedMoment B raw39515step0 raw39515step0Labels := by
      have hz : ∀ j, raw39515 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39515step0 = (fun i j => raw39515 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39515step0 raw39515; decide +kernel
      have hl : raw39515step0Labels = raw39515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39515 raw39515Labels permutation346 hz
    mixedMoment B raw39515step0 raw39515step0Labels = mixedMoment B raw39515step1 raw39515step1Labels := by
      have hz : ∀ j, raw39515step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39515step1 = (fun i j => raw39515step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39515step1 raw39515step0; decide +kernel
      have hl : raw39515step1Labels = raw39515step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39515step0 raw39515step0Labels permutation56 hz
    _ = mixedMoment B node388 node388Labels := by rfl

def raw39516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39516Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39516step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39516step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw39516step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39516step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw39516step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39516 raw39516Labels = mixedMoment B node148 node148Labels := by
  calc
    mixedMoment B raw39516 raw39516Labels = mixedMoment B raw39516step0 raw39516step0Labels := by
      have hz : ∀ j, raw39516 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39516step0 = (fun i j => raw39516 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39516step0 raw39516; decide +kernel
      have hl : raw39516step0Labels = raw39516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39516 raw39516Labels permutation346 hz
    mixedMoment B raw39516step0 raw39516step0Labels = mixedMoment B raw39516step1 raw39516step1Labels := by
      have hz : ∀ j, raw39516step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39516step1 = (fun i j => raw39516step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39516step1 raw39516step0; decide +kernel
      have hl : raw39516step1Labels = raw39516step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39516step0 raw39516step0Labels permutation56 hz
    mixedMoment B raw39516step1 raw39516step1Labels = mixedMoment B raw39516step2 raw39516step2Labels := by
      have ha : raw39516step2 = (fun i j => raw39516step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39516step2 raw39516step1; decide +kernel
      have hl : raw39516step2Labels = raw39516step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39516step1 raw39516step1Labels permutation31 permutation7
    _ = mixedMoment B node148 node148Labels := by rfl

def raw39517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw39517Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw39517step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39517step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw39517step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39517step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw39517step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39517 raw39517Labels = mixedMoment B node342 node342Labels := by
  calc
    mixedMoment B raw39517 raw39517Labels = mixedMoment B raw39517step0 raw39517step0Labels := by
      have hz : ∀ j, raw39517 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39517step0 = (fun i j => raw39517 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39517step0 raw39517; decide +kernel
      have hl : raw39517step0Labels = raw39517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39517 raw39517Labels permutation346 hz
    mixedMoment B raw39517step0 raw39517step0Labels = mixedMoment B raw39517step1 raw39517step1Labels := by
      have hz : ∀ j, raw39517step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39517step1 = (fun i j => raw39517step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39517step1 raw39517step0; decide +kernel
      have hl : raw39517step1Labels = raw39517step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39517step0 raw39517step0Labels permutation56 hz
    mixedMoment B raw39517step1 raw39517step1Labels = mixedMoment B raw39517step2 raw39517step2Labels := by
      have ha : raw39517step2 = (fun i j => raw39517step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39517step2 raw39517step1; decide +kernel
      have hl : raw39517step2Labels = raw39517step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39517step1 raw39517step1Labels permutation16 permutation6
    _ = mixedMoment B node342 node342Labels := by rfl

def raw39518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw39518Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39518step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw39518step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39518step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw39518step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39518step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw39518step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39518 raw39518Labels = mixedMoment B node406 node406Labels := by
  calc
    mixedMoment B raw39518 raw39518Labels = mixedMoment B raw39518step0 raw39518step0Labels := by
      have hz : ∀ j, raw39518 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39518step0 = (fun i j => raw39518 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39518step0 raw39518; decide +kernel
      have hl : raw39518step0Labels = raw39518Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39518 raw39518Labels permutation346 hz
    mixedMoment B raw39518step0 raw39518step0Labels = mixedMoment B raw39518step1 raw39518step1Labels := by
      have hz : ∀ j, raw39518step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39518step1 = (fun i j => raw39518step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39518step1 raw39518step0; decide +kernel
      have hl : raw39518step1Labels = raw39518step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39518step0 raw39518step0Labels permutation56 hz
    mixedMoment B raw39518step1 raw39518step1Labels = mixedMoment B raw39518step2 raw39518step2Labels := by
      have ha : raw39518step2 = (fun i j => raw39518step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39518step2 raw39518step1; decide +kernel
      have hl : raw39518step2Labels = raw39518step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39518step1 raw39518step1Labels permutation17 permutation6
    _ = mixedMoment B node406 node406Labels := by rfl

def raw39519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw39519Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw39519step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39519step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw39519step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39519step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw39519step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39519 raw39519Labels = mixedMoment B node413 node413Labels := by
  calc
    mixedMoment B raw39519 raw39519Labels = mixedMoment B raw39519step0 raw39519step0Labels := by
      have hz : ∀ j, raw39519 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39519step0 = (fun i j => raw39519 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39519step0 raw39519; decide +kernel
      have hl : raw39519step0Labels = raw39519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39519 raw39519Labels permutation346 hz
    mixedMoment B raw39519step0 raw39519step0Labels = mixedMoment B raw39519step1 raw39519step1Labels := by
      have hz : ∀ j, raw39519step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39519step1 = (fun i j => raw39519step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39519step1 raw39519step0; decide +kernel
      have hl : raw39519step1Labels = raw39519step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39519step0 raw39519step0Labels permutation56 hz
    mixedMoment B raw39519step1 raw39519step1Labels = mixedMoment B raw39519step2 raw39519step2Labels := by
      have ha : raw39519step2 = (fun i j => raw39519step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39519step2 raw39519step1; decide +kernel
      have hl : raw39519step2Labels = raw39519step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39519step1 raw39519step1Labels permutation12 permutation2
    _ = mixedMoment B node413 node413Labels := by rfl

def raw39520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39520Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39520step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39520step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39520step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39520step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw39520step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39520 raw39520Labels = mixedMoment B node416 node416Labels := by
  calc
    mixedMoment B raw39520 raw39520Labels = mixedMoment B raw39520step0 raw39520step0Labels := by
      have hz : ∀ j, raw39520 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39520step0 = (fun i j => raw39520 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39520step0 raw39520; decide +kernel
      have hl : raw39520step0Labels = raw39520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39520 raw39520Labels permutation346 hz
    mixedMoment B raw39520step0 raw39520step0Labels = mixedMoment B raw39520step1 raw39520step1Labels := by
      have hz : ∀ j, raw39520step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw39520step1 = (fun i j => raw39520step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw39520step1 raw39520step0; decide +kernel
      have hl : raw39520step1Labels = raw39520step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39520step0 raw39520step0Labels permutation56 hz
    mixedMoment B raw39520step1 raw39520step1Labels = mixedMoment B raw39520step2 raw39520step2Labels := by
      have ha : raw39520step2 = (fun i j => raw39520step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39520step2 raw39520step1; decide +kernel
      have hl : raw39520step2Labels = raw39520step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39520step1 raw39520step1Labels permutation11 permutation2
    _ = mixedMoment B node416 node416Labels := by rfl

def raw39521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39521Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw39521step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw39521step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39521 raw39521Labels = mixedMoment B node340 node340Labels := by
  calc
    mixedMoment B raw39521 raw39521Labels = mixedMoment B raw39521step0 raw39521step0Labels := by
      have hz : ∀ j, raw39521 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39521step0 = (fun i j => raw39521 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39521step0 raw39521; decide +kernel
      have hl : raw39521step0Labels = raw39521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39521 raw39521Labels permutation265 hz
    mixedMoment B raw39521step0 raw39521step0Labels = mixedMoment B raw39521step1 raw39521step1Labels := by
      have ha : raw39521step1 = (fun i j => raw39521step0 (permutation95 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39521step1 raw39521step0; decide +kernel
      have hl : raw39521step1Labels = raw39521step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39521step0 raw39521step0Labels permutation95 permutation6
    _ = mixedMoment B node340 node340Labels := by rfl

def raw39522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw39522Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39522step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw39522step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39522step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39522step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39522 raw39522Labels = mixedMoment B node387 node387Labels := by
  calc
    mixedMoment B raw39522 raw39522Labels = mixedMoment B raw39522step0 raw39522step0Labels := by
      have hz : ∀ j, raw39522 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39522step0 = (fun i j => raw39522 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39522step0 raw39522; decide +kernel
      have hl : raw39522step0Labels = raw39522Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39522 raw39522Labels permutation265 hz
    mixedMoment B raw39522step0 raw39522step0Labels = mixedMoment B raw39522step1 raw39522step1Labels := by
      have ha : raw39522step1 = (fun i j => raw39522step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39522step1 raw39522step0; decide +kernel
      have hl : raw39522step1Labels = raw39522step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39522step0 raw39522step0Labels permutation37 permutation2
    _ = mixedMoment B node387 node387Labels := by rfl

def raw39523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw39523Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw39523step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw39523step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39523 raw39523Labels = mixedMoment B node328 node328Labels := by
  calc
    mixedMoment B raw39523 raw39523Labels = mixedMoment B raw39523step0 raw39523step0Labels := by
      have hz : ∀ j, raw39523 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39523step0 = (fun i j => raw39523 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39523step0 raw39523; decide +kernel
      have hl : raw39523step0Labels = raw39523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39523 raw39523Labels permutation265 hz
    mixedMoment B raw39523step0 raw39523step0Labels = mixedMoment B raw39523step1 raw39523step1Labels := by
      have ha : raw39523step1 = (fun i j => raw39523step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39523step1 raw39523step0; decide +kernel
      have hl : raw39523step1Labels = raw39523step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39523step0 raw39523step0Labels permutation96 permutation6
    _ = mixedMoment B node328 node328Labels := by rfl

def raw39524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw39524Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw39524step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw39524step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39524 raw39524Labels = mixedMoment B node367 node367Labels := by
  calc
    mixedMoment B raw39524 raw39524Labels = mixedMoment B raw39524step0 raw39524step0Labels := by
      have hz : ∀ j, raw39524 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw39524step0 = (fun i j => raw39524 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw39524step0 raw39524; decide +kernel
      have hl : raw39524step0Labels = raw39524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39524 raw39524Labels permutation265 hz
    mixedMoment B raw39524step0 raw39524step0Labels = mixedMoment B raw39524step1 raw39524step1Labels := by
      have ha : raw39524step1 = (fun i j => raw39524step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39524step1 raw39524step0; decide +kernel
      have hl : raw39524step1Labels = raw39524step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39524step0 raw39524step0Labels permutation36 permutation2
    _ = mixedMoment B node367 node367Labels := by rfl

def raw39525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39525Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39525step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39525step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![3, -3, 0]]
def raw39525step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39525step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![3, -3, 0]]
def raw39525step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39525 raw39525Labels = mixedMoment B node271 node271Labels := by
  calc
    mixedMoment B raw39525 raw39525Labels = mixedMoment B raw39525step0 raw39525step0Labels := by
      have hz : ∀ j, raw39525 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39525step0 = (fun i j => raw39525 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39525step0 raw39525; decide +kernel
      have hl : raw39525step0Labels = raw39525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39525 raw39525Labels permutation520 hz
    mixedMoment B raw39525step0 raw39525step0Labels = mixedMoment B raw39525step1 raw39525step1Labels := by
      have hz : ∀ j, raw39525step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39525step1 = (fun i j => raw39525step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39525step1 raw39525step0; decide +kernel
      have hl : raw39525step1Labels = raw39525step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39525step0 raw39525step0Labels permutation104 hz
    mixedMoment B raw39525step1 raw39525step1Labels = mixedMoment B raw39525step2 raw39525step2Labels := by
      have hz : ∀ j, raw39525step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw39525step2 = (fun i j => raw39525step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw39525step2 raw39525step1; decide +kernel
      have hl : raw39525step2Labels = raw39525step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39525step1 raw39525step1Labels permutation20 hz
    _ = mixedMoment B node271 node271Labels := by rfl

def raw39526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39526Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39526step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39526step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39526step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw39526step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39526step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw39526step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39526 raw39526Labels = mixedMoment B node264 node264Labels := by
  calc
    mixedMoment B raw39526 raw39526Labels = mixedMoment B raw39526step0 raw39526step0Labels := by
      have hz : ∀ j, raw39526 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39526step0 = (fun i j => raw39526 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39526step0 raw39526; decide +kernel
      have hl : raw39526step0Labels = raw39526Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39526 raw39526Labels permutation434 hz
    mixedMoment B raw39526step0 raw39526step0Labels = mixedMoment B raw39526step1 raw39526step1Labels := by
      have hz : ∀ j, raw39526step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39526step1 = (fun i j => raw39526step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39526step1 raw39526step0; decide +kernel
      have hl : raw39526step1Labels = raw39526step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39526step0 raw39526step0Labels permutation80 hz
    mixedMoment B raw39526step1 raw39526step1Labels = mixedMoment B raw39526step2 raw39526step2Labels := by
      have ha : raw39526step2 = (fun i j => raw39526step1 (permutation17 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39526step2 raw39526step1; decide +kernel
      have hl : raw39526step2Labels = raw39526step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39526step1 raw39526step1Labels permutation17 permutation6
    _ = mixedMoment B node264 node264Labels := by rfl

def raw39527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39527Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39527step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw39527step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw39527step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39527 raw39527Labels = mixedMoment B node250 node250Labels := by
  calc
    mixedMoment B raw39527 raw39527Labels = mixedMoment B raw39527step0 raw39527step0Labels := by
      have hz : ∀ j, raw39527 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39527step0 = (fun i j => raw39527 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39527step0 raw39527; decide +kernel
      have hl : raw39527step0Labels = raw39527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39527 raw39527Labels permutation434 hz
    mixedMoment B raw39527step0 raw39527step0Labels = mixedMoment B raw39527step1 raw39527step1Labels := by
      have hz : ∀ j, raw39527step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39527step1 = (fun i j => raw39527step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39527step1 raw39527step0; decide +kernel
      have hl : raw39527step1Labels = raw39527step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39527step0 raw39527step0Labels permutation80 hz
    mixedMoment B raw39527step1 raw39527step1Labels = mixedMoment B raw39527step2 raw39527step2Labels := by
      have ha : raw39527step2 = (fun i j => raw39527step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39527step2 raw39527step1; decide +kernel
      have hl : raw39527step2Labels = raw39527step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39527step1 raw39527step1Labels permutation19 permutation6
    _ = mixedMoment B node250 node250Labels := by rfl

def raw39528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39528Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39528step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39528step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -3, 2], ![2, 0, -2]]
def raw39528step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39528step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def raw39528step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39528 raw39528Labels = mixedMoment B node188 node188Labels := by
  calc
    mixedMoment B raw39528 raw39528Labels = mixedMoment B raw39528step0 raw39528step0Labels := by
      have hz : ∀ j, raw39528 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39528step0 = (fun i j => raw39528 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39528step0 raw39528; decide +kernel
      have hl : raw39528step0Labels = raw39528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39528 raw39528Labels permutation434 hz
    mixedMoment B raw39528step0 raw39528step0Labels = mixedMoment B raw39528step1 raw39528step1Labels := by
      have hz : ∀ j, raw39528step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39528step1 = (fun i j => raw39528step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39528step1 raw39528step0; decide +kernel
      have hl : raw39528step1Labels = raw39528step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39528step0 raw39528step0Labels permutation80 hz
    mixedMoment B raw39528step1 raw39528step1Labels = mixedMoment B raw39528step2 raw39528step2Labels := by
      have ha : raw39528step2 = (fun i j => raw39528step1 (permutation19 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39528step2 raw39528step1; decide +kernel
      have hl : raw39528step2Labels = raw39528step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39528step1 raw39528step1Labels permutation19 permutation6
    _ = mixedMoment B node188 node188Labels := by rfl

def raw39529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39529Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw39529step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw39529step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39529 raw39529Labels = mixedMoment B node228 node228Labels := by
  calc
    mixedMoment B raw39529 raw39529Labels = mixedMoment B raw39529step0 raw39529step0Labels := by
      have hz : ∀ j, raw39529 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39529step0 = (fun i j => raw39529 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39529step0 raw39529; decide +kernel
      have hl : raw39529step0Labels = raw39529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39529 raw39529Labels permutation346 hz
    mixedMoment B raw39529step0 raw39529step0Labels = mixedMoment B raw39529step1 raw39529step1Labels := by
      have ha : raw39529step1 = (fun i j => raw39529step0 (permutation73 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39529step1 raw39529step0; decide +kernel
      have hl : raw39529step1Labels = raw39529step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39529step0 raw39529step0Labels permutation73 permutation6
    _ = mixedMoment B node228 node228Labels := by rfl

def raw39530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39530Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw39530step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw39530step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39530step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw39530step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39530 raw39530Labels = mixedMoment B node225 node225Labels := by
  calc
    mixedMoment B raw39530 raw39530Labels = mixedMoment B raw39530step0 raw39530step0Labels := by
      have hz : ∀ j, raw39530 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39530step0 = (fun i j => raw39530 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39530step0 raw39530; decide +kernel
      have hl : raw39530step0Labels = raw39530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39530 raw39530Labels permutation346 hz
    mixedMoment B raw39530step0 raw39530step0Labels = mixedMoment B raw39530step1 raw39530step1Labels := by
      have ha : raw39530step1 = (fun i j => raw39530step0 (permutation41 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39530step1 raw39530step0; decide +kernel
      have hl : raw39530step1Labels = raw39530step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39530step0 raw39530step0Labels permutation41 permutation7
    mixedMoment B raw39530step1 raw39530step1Labels = mixedMoment B raw39530step2 raw39530step2Labels := by
      have ha : raw39530step2 = -raw39530step1 := by apply Matrix.ext; change ∀ i j, raw39530step2 i j = -(raw39530step1 i j); unfold raw39530step2 raw39530step1; decide +kernel
      have hl : raw39530step2Labels = raw39530step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node225 node225Labels := by rfl

def raw39531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39531Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw39531step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw39531step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39531 raw39531Labels = mixedMoment B node181 node181Labels := by
  calc
    mixedMoment B raw39531 raw39531Labels = mixedMoment B raw39531step0 raw39531step0Labels := by
      have hz : ∀ j, raw39531 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39531step0 = (fun i j => raw39531 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39531step0 raw39531; decide +kernel
      have hl : raw39531step0Labels = raw39531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39531 raw39531Labels permutation346 hz
    mixedMoment B raw39531step0 raw39531step0Labels = mixedMoment B raw39531step1 raw39531step1Labels := by
      have ha : raw39531step1 = (fun i j => raw39531step0 (permutation77 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39531step1 raw39531step0; decide +kernel
      have hl : raw39531step1Labels = raw39531step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39531step0 raw39531step0Labels permutation77 permutation6
    _ = mixedMoment B node181 node181Labels := by rfl

def raw39532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39532Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39532step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw39532step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39532 raw39532Labels = mixedMoment B node170 node170Labels := by
  calc
    mixedMoment B raw39532 raw39532Labels = mixedMoment B raw39532step0 raw39532step0Labels := by
      have hz : ∀ j, raw39532 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39532step0 = (fun i j => raw39532 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39532step0 raw39532; decide +kernel
      have hl : raw39532step0Labels = raw39532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39532 raw39532Labels permutation346 hz
    mixedMoment B raw39532step0 raw39532step0Labels = mixedMoment B raw39532step1 raw39532step1Labels := by
      have ha : raw39532step1 = (fun i j => raw39532step0 (permutation79 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39532step1 raw39532step0; decide +kernel
      have hl : raw39532step1Labels = raw39532step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39532step0 raw39532step0Labels permutation79 permutation6
    _ = mixedMoment B node170 node170Labels := by rfl

def raw39533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw39533Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw39533step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw39533step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39533step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw39533step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39533 raw39533Labels = mixedMoment B node194 node194Labels := by
  calc
    mixedMoment B raw39533 raw39533Labels = mixedMoment B raw39533step0 raw39533step0Labels := by
      have hz : ∀ j, raw39533 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39533step0 = (fun i j => raw39533 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39533step0 raw39533; decide +kernel
      have hl : raw39533step0Labels = raw39533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39533 raw39533Labels permutation346 hz
    mixedMoment B raw39533step0 raw39533step0Labels = mixedMoment B raw39533step1 raw39533step1Labels := by
      have ha : raw39533step1 = (fun i j => raw39533step0 (permutation53 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39533step1 raw39533step0; decide +kernel
      have hl : raw39533step1Labels = raw39533step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39533step0 raw39533step0Labels permutation53 permutation7
    mixedMoment B raw39533step1 raw39533step1Labels = mixedMoment B raw39533step2 raw39533step2Labels := by
      have ha : raw39533step2 = -raw39533step1 := by apply Matrix.ext; change ∀ i j, raw39533step2 i j = -(raw39533step1 i j); unfold raw39533step2 raw39533step1; decide +kernel
      have hl : raw39533step2Labels = raw39533step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node194 node194Labels := by rfl

def raw39534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39534Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw39534step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw39534step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39534 raw39534Labels = mixedMoment B node225 node225Labels := by
  calc
    mixedMoment B raw39534 raw39534Labels = mixedMoment B raw39534step0 raw39534step0Labels := by
      have hz : ∀ j, raw39534 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39534step0 = (fun i j => raw39534 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39534step0 raw39534; decide +kernel
      have hl : raw39534step0Labels = raw39534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39534 raw39534Labels permutation346 hz
    mixedMoment B raw39534step0 raw39534step0Labels = mixedMoment B raw39534step1 raw39534step1Labels := by
      have ha : raw39534step1 = (fun i j => raw39534step0 (permutation65 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39534step1 raw39534step0; decide +kernel
      have hl : raw39534step1Labels = raw39534step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39534step0 raw39534step0Labels permutation65 permutation6
    _ = mixedMoment B node225 node225Labels := by rfl

def raw39535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39535Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw39535step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw39535step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39535 raw39535Labels = mixedMoment B node258 node258Labels := by
  calc
    mixedMoment B raw39535 raw39535Labels = mixedMoment B raw39535step0 raw39535step0Labels := by
      have hz : ∀ j, raw39535 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39535step0 = (fun i j => raw39535 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39535step0 raw39535; decide +kernel
      have hl : raw39535step0Labels = raw39535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39535 raw39535Labels permutation346 hz
    mixedMoment B raw39535step0 raw39535step0Labels = mixedMoment B raw39535step1 raw39535step1Labels := by
      have ha : raw39535step1 = (fun i j => raw39535step0 (permutation65 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39535step1 raw39535step0; decide +kernel
      have hl : raw39535step1Labels = raw39535step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39535step0 raw39535step0Labels permutation65 permutation6
    _ = mixedMoment B node258 node258Labels := by rfl

def raw39536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw39536Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw39536step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39536 raw39536Labels = mixedMoment B node166 node166Labels := by
  calc
    mixedMoment B raw39536 raw39536Labels = mixedMoment B raw39536step0 raw39536step0Labels := by
      have ha : raw39536step0 = (fun i j => raw39536 (permutation345 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39536step0 raw39536; decide +kernel
      have hl : raw39536step0Labels = raw39536Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39536 raw39536Labels permutation345 permutation6
    _ = mixedMoment B node166 node166Labels := by rfl

def raw39537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw39537Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw39537step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39537 raw39537Labels = mixedMoment B node208 node208Labels := by
  calc
    mixedMoment B raw39537 raw39537Labels = mixedMoment B raw39537step0 raw39537step0Labels := by
      have ha : raw39537step0 = (fun i j => raw39537 (permutation316 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39537step0 raw39537; decide +kernel
      have hl : raw39537step0Labels = raw39537Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39537 raw39537Labels permutation316 permutation6
    _ = mixedMoment B node208 node208Labels := by rfl

def raw39538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw39538Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw39538step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39538 raw39538Labels = mixedMoment B node218 node218Labels := by
  calc
    mixedMoment B raw39538 raw39538Labels = mixedMoment B raw39538step0 raw39538step0Labels := by
      have ha : raw39538step0 = (fun i j => raw39538 (permutation317 i) (permutation6 j)) := by apply Matrix.ext; unfold raw39538step0 raw39538; decide +kernel
      have hl : raw39538step0Labels = raw39538Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39538 raw39538Labels permutation317 permutation6
    _ = mixedMoment B node218 node218Labels := by rfl

def raw39539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw39539Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw39539step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39539step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw39539step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39539 raw39539Labels = mixedMoment B node166 node166Labels := by
  calc
    mixedMoment B raw39539 raw39539Labels = mixedMoment B raw39539step0 raw39539step0Labels := by
      have ha : raw39539step0 = (fun i j => raw39539 (permutation197 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39539step0 raw39539; decide +kernel
      have hl : raw39539step0Labels = raw39539Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39539 raw39539Labels permutation197 permutation7
    mixedMoment B raw39539step0 raw39539step0Labels = mixedMoment B raw39539step1 raw39539step1Labels := by
      have ha : raw39539step1 = -raw39539step0 := by apply Matrix.ext; change ∀ i j, raw39539step1 i j = -(raw39539step0 i j); unfold raw39539step1 raw39539step0; decide +kernel
      have hl : raw39539step1Labels = raw39539step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node166 node166Labels := by rfl

def raw39540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw39540Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw39540step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39540step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![3, -3, 0]]
def raw39540step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39540step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw39540step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39540 raw39540Labels = mixedMoment B node264 node264Labels := by
  calc
    mixedMoment B raw39540 raw39540Labels = mixedMoment B raw39540step0 raw39540step0Labels := by
      have hz : ∀ j, raw39540 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw39540step0 = (fun i j => raw39540 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw39540step0 raw39540; decide +kernel
      have hl : raw39540step0Labels = raw39540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39540 raw39540Labels permutation520 hz
    mixedMoment B raw39540step0 raw39540step0Labels = mixedMoment B raw39540step1 raw39540step1Labels := by
      have hz : ∀ j, raw39540step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw39540step1 = (fun i j => raw39540step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw39540step1 raw39540step0; decide +kernel
      have hl : raw39540step1Labels = raw39540step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39540step0 raw39540step0Labels permutation104 hz
    mixedMoment B raw39540step1 raw39540step1Labels = mixedMoment B raw39540step2 raw39540step2Labels := by
      have ha : raw39540step2 = (fun i j => raw39540step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39540step2 raw39540step1; decide +kernel
      have hl : raw39540step2Labels = raw39540step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39540step1 raw39540step1Labels permutation10 permutation2
    _ = mixedMoment B node264 node264Labels := by rfl

def raw39541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39541Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw39541step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw39541step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39541 raw39541Labels = mixedMoment B node263 node263Labels := by
  calc
    mixedMoment B raw39541 raw39541Labels = mixedMoment B raw39541step0 raw39541step0Labels := by
      have hz : ∀ j, raw39541 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39541step0 = (fun i j => raw39541 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39541step0 raw39541; decide +kernel
      have hl : raw39541step0Labels = raw39541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39541 raw39541Labels permutation434 hz
    mixedMoment B raw39541step0 raw39541step0Labels = mixedMoment B raw39541step1 raw39541step1Labels := by
      have ha : raw39541step1 = (fun i j => raw39541step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw39541step1 raw39541step0; decide +kernel
      have hl : raw39541step1Labels = raw39541step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39541step0 raw39541step0Labels permutation38 permutation2
    _ = mixedMoment B node263 node263Labels := by rfl

def raw39542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw39542Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw39542step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw39542step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw39542step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39542 raw39542Labels = mixedMoment B node246 node246Labels := by
  calc
    mixedMoment B raw39542 raw39542Labels = mixedMoment B raw39542step0 raw39542step0Labels := by
      have hz : ∀ j, raw39542 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39542step0 = (fun i j => raw39542 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39542step0 raw39542; decide +kernel
      have hl : raw39542step0Labels = raw39542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39542 raw39542Labels permutation434 hz
    mixedMoment B raw39542step0 raw39542step0Labels = mixedMoment B raw39542step1 raw39542step1Labels := by
      have ha : raw39542step1 = (fun i j => raw39542step0 (permutation47 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39542step1 raw39542step0; decide +kernel
      have hl : raw39542step1Labels = raw39542step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39542step0 raw39542step0Labels permutation47 permutation7
    mixedMoment B raw39542step1 raw39542step1Labels = mixedMoment B raw39542step2 raw39542step2Labels := by
      have ha : raw39542step2 = -raw39542step1 := by apply Matrix.ext; change ∀ i j, raw39542step2 i j = -(raw39542step1 i j); unfold raw39542step2 raw39542step1; decide +kernel
      have hl : raw39542step2Labels = raw39542step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node246 node246Labels := by rfl

def raw39543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw39543Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw39543step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw39543step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39543step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39543 raw39543Labels = mixedMoment B node193 node193Labels := by
  calc
    mixedMoment B raw39543 raw39543Labels = mixedMoment B raw39543step0 raw39543step0Labels := by
      have hz : ∀ j, raw39543 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39543step0 = (fun i j => raw39543 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39543step0 raw39543; decide +kernel
      have hl : raw39543step0Labels = raw39543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39543 raw39543Labels permutation434 hz
    mixedMoment B raw39543step0 raw39543step0Labels = mixedMoment B raw39543step1 raw39543step1Labels := by
      have ha : raw39543step1 = (fun i j => raw39543step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39543step1 raw39543step0; decide +kernel
      have hl : raw39543step1Labels = raw39543step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39543step0 raw39543step0Labels permutation46 permutation7
    mixedMoment B raw39543step1 raw39543step1Labels = mixedMoment B raw39543step2 raw39543step2Labels := by
      have ha : raw39543step2 = -raw39543step1 := by apply Matrix.ext; change ∀ i j, raw39543step2 i j = -(raw39543step1 i j); unfold raw39543step2 raw39543step1; decide +kernel
      have hl : raw39543step2Labels = raw39543step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node193 node193Labels := by rfl

def raw39544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw39544Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw39544step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39544step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39544 raw39544Labels = mixedMoment B node165 node165Labels := by
  calc
    mixedMoment B raw39544 raw39544Labels = mixedMoment B raw39544step0 raw39544step0Labels := by
      have ha : raw39544step0 = (fun i j => raw39544 (permutation214 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39544step0 raw39544; decide +kernel
      have hl : raw39544step0Labels = raw39544Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39544 raw39544Labels permutation214 permutation7
    mixedMoment B raw39544step0 raw39544step0Labels = mixedMoment B raw39544step1 raw39544step1Labels := by
      have ha : raw39544step1 = -raw39544step0 := by apply Matrix.ext; change ∀ i j, raw39544step1 i j = -(raw39544step0 i j); unfold raw39544step1 raw39544step0; decide +kernel
      have hl : raw39544step1Labels = raw39544step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node165 node165Labels := by rfl

def raw39545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw39545Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw39545step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39545step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39545 raw39545Labels = mixedMoment B node191 node191Labels := by
  calc
    mixedMoment B raw39545 raw39545Labels = mixedMoment B raw39545step0 raw39545step0Labels := by
      have ha : raw39545step0 = (fun i j => raw39545 (permutation255 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39545step0 raw39545; decide +kernel
      have hl : raw39545step0Labels = raw39545Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39545 raw39545Labels permutation255 permutation7
    mixedMoment B raw39545step0 raw39545step0Labels = mixedMoment B raw39545step1 raw39545step1Labels := by
      have ha : raw39545step1 = -raw39545step0 := by apply Matrix.ext; change ∀ i j, raw39545step1 i j = -(raw39545step0 i j); unfold raw39545step1 raw39545step0; decide +kernel
      have hl : raw39545step1Labels = raw39545step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node191 node191Labels := by rfl

def raw39546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw39546Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw39546step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![2, -3, 1]]
def raw39546step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw39546step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39546step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39546step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39546 raw39546Labels = mixedMoment B node256 node256Labels := by
  calc
    mixedMoment B raw39546 raw39546Labels = mixedMoment B raw39546step0 raw39546step0Labels := by
      have hz : ∀ j, raw39546 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39546step0 = (fun i j => raw39546 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39546step0 raw39546; decide +kernel
      have hl : raw39546step0Labels = raw39546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39546 raw39546Labels permutation434 hz
    mixedMoment B raw39546step0 raw39546step0Labels = mixedMoment B raw39546step1 raw39546step1Labels := by
      have hz : ∀ j, raw39546step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39546step1 = (fun i j => raw39546step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39546step1 raw39546step0; decide +kernel
      have hl : raw39546step1Labels = raw39546step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39546step0 raw39546step0Labels permutation80 hz
    mixedMoment B raw39546step1 raw39546step1Labels = mixedMoment B raw39546step2 raw39546step2Labels := by
      have ha : raw39546step2 = (fun i j => raw39546step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39546step2 raw39546step1; decide +kernel
      have hl : raw39546step2Labels = raw39546step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39546step1 raw39546step1Labels permutation12 permutation7
    mixedMoment B raw39546step2 raw39546step2Labels = mixedMoment B raw39546step3 raw39546step3Labels := by
      have ha : raw39546step3 = -raw39546step2 := by apply Matrix.ext; change ∀ i j, raw39546step3 i j = -(raw39546step2 i j); unfold raw39546step3 raw39546step2; decide +kernel
      have hl : raw39546step3Labels = raw39546step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node256 node256Labels := by rfl

def raw39547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39547Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw39547step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39547step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw39547step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39547step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw39547step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39547step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39547step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39547 raw39547Labels = mixedMoment B node268 node268Labels := by
  calc
    mixedMoment B raw39547 raw39547Labels = mixedMoment B raw39547step0 raw39547step0Labels := by
      have hz : ∀ j, raw39547 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39547step0 = (fun i j => raw39547 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39547step0 raw39547; decide +kernel
      have hl : raw39547step0Labels = raw39547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39547 raw39547Labels permutation434 hz
    mixedMoment B raw39547step0 raw39547step0Labels = mixedMoment B raw39547step1 raw39547step1Labels := by
      have hz : ∀ j, raw39547step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39547step1 = (fun i j => raw39547step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39547step1 raw39547step0; decide +kernel
      have hl : raw39547step1Labels = raw39547step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39547step0 raw39547step0Labels permutation80 hz
    mixedMoment B raw39547step1 raw39547step1Labels = mixedMoment B raw39547step2 raw39547step2Labels := by
      have ha : raw39547step2 = (fun i j => raw39547step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39547step2 raw39547step1; decide +kernel
      have hl : raw39547step2Labels = raw39547step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39547step1 raw39547step1Labels permutation11 permutation7
    mixedMoment B raw39547step2 raw39547step2Labels = mixedMoment B raw39547step3 raw39547step3Labels := by
      have ha : raw39547step3 = -raw39547step2 := by apply Matrix.ext; change ∀ i j, raw39547step3 i j = -(raw39547step2 i j); unfold raw39547step3 raw39547step2; decide +kernel
      have hl : raw39547step3Labels = raw39547step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node268 node268Labels := by rfl

def raw39548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39548Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw39548step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39548step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw39548step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39548step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw39548step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39548step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39548step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39548 raw39548Labels = mixedMoment B node251 node251Labels := by
  calc
    mixedMoment B raw39548 raw39548Labels = mixedMoment B raw39548step0 raw39548step0Labels := by
      have hz : ∀ j, raw39548 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39548step0 = (fun i j => raw39548 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39548step0 raw39548; decide +kernel
      have hl : raw39548step0Labels = raw39548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39548 raw39548Labels permutation434 hz
    mixedMoment B raw39548step0 raw39548step0Labels = mixedMoment B raw39548step1 raw39548step1Labels := by
      have hz : ∀ j, raw39548step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39548step1 = (fun i j => raw39548step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39548step1 raw39548step0; decide +kernel
      have hl : raw39548step1Labels = raw39548step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39548step0 raw39548step0Labels permutation80 hz
    mixedMoment B raw39548step1 raw39548step1Labels = mixedMoment B raw39548step2 raw39548step2Labels := by
      have ha : raw39548step2 = (fun i j => raw39548step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39548step2 raw39548step1; decide +kernel
      have hl : raw39548step2Labels = raw39548step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39548step1 raw39548step1Labels permutation10 permutation7
    mixedMoment B raw39548step2 raw39548step2Labels = mixedMoment B raw39548step3 raw39548step3Labels := by
      have ha : raw39548step3 = -raw39548step2 := by apply Matrix.ext; change ∀ i j, raw39548step3 i j = -(raw39548step2 i j); unfold raw39548step3 raw39548step2; decide +kernel
      have hl : raw39548step3Labels = raw39548step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node251 node251Labels := by rfl

def raw39549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw39549Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw39549step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39549step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw39549step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39549step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -3, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw39549step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39549step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw39549step3Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39549 raw39549Labels = mixedMoment B node196 node196Labels := by
  calc
    mixedMoment B raw39549 raw39549Labels = mixedMoment B raw39549step0 raw39549step0Labels := by
      have hz : ∀ j, raw39549 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw39549step0 = (fun i j => raw39549 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw39549step0 raw39549; decide +kernel
      have hl : raw39549step0Labels = raw39549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39549 raw39549Labels permutation434 hz
    mixedMoment B raw39549step0 raw39549step0Labels = mixedMoment B raw39549step1 raw39549step1Labels := by
      have hz : ∀ j, raw39549step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw39549step1 = (fun i j => raw39549step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw39549step1 raw39549step0; decide +kernel
      have hl : raw39549step1Labels = raw39549step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39549step0 raw39549step0Labels permutation80 hz
    mixedMoment B raw39549step1 raw39549step1Labels = mixedMoment B raw39549step2 raw39549step2Labels := by
      have ha : raw39549step2 = (fun i j => raw39549step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39549step2 raw39549step1; decide +kernel
      have hl : raw39549step2Labels = raw39549step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39549step1 raw39549step1Labels permutation10 permutation7
    mixedMoment B raw39549step2 raw39549step2Labels = mixedMoment B raw39549step3 raw39549step3Labels := by
      have ha : raw39549step3 = -raw39549step2 := by apply Matrix.ext; change ∀ i j, raw39549step3 i j = -(raw39549step2 i j); unfold raw39549step3 raw39549step2; decide +kernel
      have hl : raw39549step3Labels = raw39549step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node196 node196Labels := by rfl

def raw39550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw39550Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw39550step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw39550step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39550step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw39550step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39550 raw39550Labels = mixedMoment B node229 node229Labels := by
  calc
    mixedMoment B raw39550 raw39550Labels = mixedMoment B raw39550step0 raw39550step0Labels := by
      have hz : ∀ j, raw39550 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39550step0 = (fun i j => raw39550 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39550step0 raw39550; decide +kernel
      have hl : raw39550step0Labels = raw39550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39550 raw39550Labels permutation346 hz
    mixedMoment B raw39550step0 raw39550step0Labels = mixedMoment B raw39550step1 raw39550step1Labels := by
      have ha : raw39550step1 = (fun i j => raw39550step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39550step1 raw39550step0; decide +kernel
      have hl : raw39550step1Labels = raw39550step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39550step0 raw39550step0Labels permutation42 permutation7
    mixedMoment B raw39550step1 raw39550step1Labels = mixedMoment B raw39550step2 raw39550step2Labels := by
      have ha : raw39550step2 = -raw39550step1 := by apply Matrix.ext; change ∀ i j, raw39550step2 i j = -(raw39550step1 i j); unfold raw39550step2 raw39550step1; decide +kernel
      have hl : raw39550step2Labels = raw39550step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node229 node229Labels := by rfl

def raw39551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw39551Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw39551step0Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39551step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -2, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw39551step1Labels : Fin 3 → Fin 1 := ![0, 0, 0]

def raw39551step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw39551step2Labels : Fin 3 → Fin 1 := ![0, 0, 0]

theorem canonical39551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39551 raw39551Labels = mixedMoment B node214 node214Labels := by
  calc
    mixedMoment B raw39551 raw39551Labels = mixedMoment B raw39551step0 raw39551step0Labels := by
      have hz : ∀ j, raw39551 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw39551step0 = (fun i j => raw39551 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw39551step0 raw39551; decide +kernel
      have hl : raw39551step0Labels = raw39551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw39551 raw39551Labels permutation346 hz
    mixedMoment B raw39551step0 raw39551step0Labels = mixedMoment B raw39551step1 raw39551step1Labels := by
      have ha : raw39551step1 = (fun i j => raw39551step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39551step1 raw39551step0; decide +kernel
      have hl : raw39551step1Labels = raw39551step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39551step0 raw39551step0Labels permutation40 permutation7
    mixedMoment B raw39551step1 raw39551step1Labels = mixedMoment B raw39551step2 raw39551step2Labels := by
      have ha : raw39551step2 = -raw39551step1 := by apply Matrix.ext; change ∀ i j, raw39551step2 i j = -(raw39551step1 i j); unfold raw39551step2 raw39551step1; decide +kernel
      have hl : raw39551step2Labels = raw39551step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node214 node214Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
