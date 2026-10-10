import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw27008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw27008Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27008 raw27008Labels = mixedMoment B node977 node977Labels := by
  calc
    mixedMoment B raw27008 raw27008Labels = mixedMoment B raw27008step0 raw27008step0Labels := by
      have ha : raw27008step0 = (fun i j => raw27008 (permutation250 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27008step0 raw27008; decide +kernel
      have hl : raw27008step0Labels = raw27008Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27008 raw27008Labels permutation250 permutation3
    _ = mixedMoment B node977 node977Labels := by rfl

def raw27009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw27009Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27009step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27009 raw27009Labels = mixedMoment B node537 node537Labels := by
  calc
    mixedMoment B raw27009 raw27009Labels = mixedMoment B raw27009step0 raw27009step0Labels := by
      have ha : raw27009step0 = (fun i j => raw27009 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27009step0 raw27009; decide +kernel
      have hl : raw27009step0Labels = raw27009Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27009 raw27009Labels permutation170 permutation3
    _ = mixedMoment B node537 node537Labels := by rfl

def raw27010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw27010Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27010 raw27010Labels = mixedMoment B node922 node922Labels := by
  calc
    mixedMoment B raw27010 raw27010Labels = mixedMoment B raw27010step0 raw27010step0Labels := by
      have ha : raw27010step0 = (fun i j => raw27010 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27010step0 raw27010; decide +kernel
      have hl : raw27010step0Labels = raw27010Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27010 raw27010Labels permutation170 permutation3
    _ = mixedMoment B node922 node922Labels := by rfl

def raw27011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw27011Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw27011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27011 raw27011Labels = mixedMoment B node980 node980Labels := by
  calc
    mixedMoment B raw27011 raw27011Labels = mixedMoment B raw27011step0 raw27011step0Labels := by
      have ha : raw27011step0 = (fun i j => raw27011 (permutation246 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27011step0 raw27011; decide +kernel
      have hl : raw27011step0Labels = raw27011Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27011 raw27011Labels permutation246 permutation3
    _ = mixedMoment B node980 node980Labels := by rfl

def raw27012 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27012step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27012step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27012step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27012step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27012 raw27012Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw27012 raw27012Labels = mixedMoment B raw27012step0 raw27012step0Labels := by
      have ha : raw27012step0 = (fun i j => raw27012 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27012step0 raw27012; decide +kernel
      have hl : raw27012step0Labels = raw27012Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27012 raw27012Labels permutation158 permutation7
    mixedMoment B raw27012step0 raw27012step0Labels = mixedMoment B raw27012step1 raw27012step1Labels := by
      have ha : raw27012step1 = raw27012step0 := by apply Matrix.ext; unfold raw27012step1 raw27012step0; decide +kernel
      have hl : raw27012step0Labels = labelEmbedding10 ∘ raw27012step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27012step0 raw27012step0Labels raw27012step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

def raw27013 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27013step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27013step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27013step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27013 raw27013Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw27013 raw27013Labels = mixedMoment B raw27013step0 raw27013step0Labels := by
      have ha : raw27013step0 = (fun i j => raw27013 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27013step0 raw27013; decide +kernel
      have hl : raw27013step0Labels = raw27013Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27013 raw27013Labels permutation152 permutation7
    mixedMoment B raw27013step0 raw27013step0Labels = mixedMoment B raw27013step1 raw27013step1Labels := by
      have ha : raw27013step1 = raw27013step0 := by apply Matrix.ext; unfold raw27013step1 raw27013step0; decide +kernel
      have hl : raw27013step0Labels = labelEmbedding10 ∘ raw27013step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27013step0 raw27013step0Labels raw27013step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

def raw27014 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw27014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27014step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27014step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27014step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27014step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27014 raw27014Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw27014 raw27014Labels = mixedMoment B raw27014step0 raw27014step0Labels := by
      have ha : raw27014step0 = (fun i j => raw27014 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27014step0 raw27014; decide +kernel
      have hl : raw27014step0Labels = raw27014Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27014 raw27014Labels permutation153 permutation7
    mixedMoment B raw27014step0 raw27014step0Labels = mixedMoment B raw27014step1 raw27014step1Labels := by
      have ha : raw27014step1 = raw27014step0 := by apply Matrix.ext; unfold raw27014step1 raw27014step0; decide +kernel
      have hl : raw27014step0Labels = labelEmbedding10 ∘ raw27014step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27014step0 raw27014step0Labels raw27014step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw27015 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27015step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27015step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27015step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27015step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27015 raw27015Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw27015 raw27015Labels = mixedMoment B raw27015step0 raw27015step0Labels := by
      have ha : raw27015step0 = (fun i j => raw27015 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27015step0 raw27015; decide +kernel
      have hl : raw27015step0Labels = raw27015Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27015 raw27015Labels permutation152 permutation7
    mixedMoment B raw27015step0 raw27015step0Labels = mixedMoment B raw27015step1 raw27015step1Labels := by
      have ha : raw27015step1 = raw27015step0 := by apply Matrix.ext; unfold raw27015step1 raw27015step0; decide +kernel
      have hl : raw27015step0Labels = labelEmbedding10 ∘ raw27015step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27015step0 raw27015step0Labels raw27015step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw27016 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27016step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27016step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27016step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27016step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27016step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27016step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27016 raw27016Labels = mixedMoment B node4252 node4252Labels := by
  calc
    mixedMoment B raw27016 raw27016Labels = mixedMoment B raw27016step0 raw27016step0Labels := by
      have ha : raw27016step0 = (fun i j => raw27016 (permutation243 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27016step0 raw27016; decide +kernel
      have hl : raw27016step0Labels = raw27016Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27016 raw27016Labels permutation243 permutation4
    mixedMoment B raw27016step0 raw27016step0Labels = mixedMoment B raw27016step1 raw27016step1Labels := by
      have ha : raw27016step1 = -raw27016step0 := by apply Matrix.ext; change ∀ i j, raw27016step1 i j = -(raw27016step0 i j); unfold raw27016step1 raw27016step0; decide +kernel
      have hl : raw27016step1Labels = raw27016step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27016step1 raw27016step1Labels = mixedMoment B raw27016step2 raw27016step2Labels := by
      have ha : raw27016step2 = raw27016step1 := by apply Matrix.ext; unfold raw27016step2 raw27016step1; decide +kernel
      have hl : raw27016step1Labels = labelEmbedding7 ∘ raw27016step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27016step1 raw27016step1Labels raw27016step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4252 node4252Labels := by rfl

def raw27017 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27017step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw27017step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27017step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw27017step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27017 raw27017Labels = mixedMoment B node4473 node4473Labels := by
  calc
    mixedMoment B raw27017 raw27017Labels = mixedMoment B raw27017step0 raw27017step0Labels := by
      have ha : raw27017step0 = (fun i j => raw27017 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27017step0 raw27017; decide +kernel
      have hl : raw27017step0Labels = raw27017Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27017 raw27017Labels permutation155 permutation6
    mixedMoment B raw27017step0 raw27017step0Labels = mixedMoment B raw27017step1 raw27017step1Labels := by
      have ha : raw27017step1 = raw27017step0 := by apply Matrix.ext; unfold raw27017step1 raw27017step0; decide +kernel
      have hl : raw27017step0Labels = labelEmbedding9 ∘ raw27017step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27017step0 raw27017step0Labels raw27017step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4473 node4473Labels := by rfl

def raw27018 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27018step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw27018step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27018step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw27018step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27018 raw27018Labels = mixedMoment B node4473 node4473Labels := by
  calc
    mixedMoment B raw27018 raw27018Labels = mixedMoment B raw27018step0 raw27018step0Labels := by
      have ha : raw27018step0 = (fun i j => raw27018 (permutation161 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27018step0 raw27018; decide +kernel
      have hl : raw27018step0Labels = raw27018Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27018 raw27018Labels permutation161 permutation6
    mixedMoment B raw27018step0 raw27018step0Labels = mixedMoment B raw27018step1 raw27018step1Labels := by
      have ha : raw27018step1 = raw27018step0 := by apply Matrix.ext; unfold raw27018step1 raw27018step0; decide +kernel
      have hl : raw27018step0Labels = labelEmbedding9 ∘ raw27018step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27018step0 raw27018step0Labels raw27018step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4473 node4473Labels := by rfl

def raw27019 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw27019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27019step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27019step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27019step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27019 raw27019Labels = mixedMoment B node4469 node4469Labels := by
  calc
    mixedMoment B raw27019 raw27019Labels = mixedMoment B raw27019step0 raw27019step0Labels := by
      have ha : raw27019step0 = (fun i j => raw27019 (permutation168 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27019step0 raw27019; decide +kernel
      have hl : raw27019step0Labels = raw27019Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27019 raw27019Labels permutation168 permutation6
    mixedMoment B raw27019step0 raw27019step0Labels = mixedMoment B raw27019step1 raw27019step1Labels := by
      have ha : raw27019step1 = raw27019step0 := by apply Matrix.ext; unfold raw27019step1 raw27019step0; decide +kernel
      have hl : raw27019step0Labels = labelEmbedding9 ∘ raw27019step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27019step0 raw27019step0Labels raw27019step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4469 node4469Labels := by rfl

def raw27020 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27020step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27020step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27020step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27020 raw27020Labels = mixedMoment B node4469 node4469Labels := by
  calc
    mixedMoment B raw27020 raw27020Labels = mixedMoment B raw27020step0 raw27020step0Labels := by
      have ha : raw27020step0 = (fun i j => raw27020 (permutation174 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27020step0 raw27020; decide +kernel
      have hl : raw27020step0Labels = raw27020Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27020 raw27020Labels permutation174 permutation6
    mixedMoment B raw27020step0 raw27020step0Labels = mixedMoment B raw27020step1 raw27020step1Labels := by
      have ha : raw27020step1 = raw27020step0 := by apply Matrix.ext; unfold raw27020step1 raw27020step0; decide +kernel
      have hl : raw27020step0Labels = labelEmbedding9 ∘ raw27020step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27020step0 raw27020step0Labels raw27020step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4469 node4469Labels := by rfl

def raw27021 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw27021step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27021step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27021step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27021step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27021step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27021 raw27021Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw27021 raw27021Labels = mixedMoment B raw27021step0 raw27021step0Labels := by
      have ha : raw27021step0 = (fun i j => raw27021 (permutation241 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27021step0 raw27021; decide +kernel
      have hl : raw27021step0Labels = raw27021Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27021 raw27021Labels permutation241 permutation4
    mixedMoment B raw27021step0 raw27021step0Labels = mixedMoment B raw27021step1 raw27021step1Labels := by
      have ha : raw27021step1 = -raw27021step0 := by apply Matrix.ext; change ∀ i j, raw27021step1 i j = -(raw27021step0 i j); unfold raw27021step1 raw27021step0; decide +kernel
      have hl : raw27021step1Labels = raw27021step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27021step1 raw27021step1Labels = mixedMoment B raw27021step2 raw27021step2Labels := by
      have ha : raw27021step2 = raw27021step1 := by apply Matrix.ext; unfold raw27021step2 raw27021step1; decide +kernel
      have hl : raw27021step1Labels = labelEmbedding7 ∘ raw27021step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27021step1 raw27021step1Labels raw27021step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4249 node4249Labels := by rfl

def raw27022 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27022step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27022step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27022 raw27022Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw27022 raw27022Labels = mixedMoment B raw27022step0 raw27022step0Labels := by
      have hz : ∀ j, raw27022 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27022step0 = (fun i j => raw27022 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27022step0 raw27022; decide +kernel
      have hl : raw27022step0Labels = raw27022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27022 raw27022Labels permutation265 hz
    mixedMoment B raw27022step0 raw27022step0Labels = mixedMoment B raw27022step1 raw27022step1Labels := by
      have ha : raw27022step1 = (fun i j => raw27022step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27022step1 raw27022step0; decide +kernel
      have hl : raw27022step1Labels = raw27022step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27022step0 raw27022step0Labels permutation49 permutation6
    mixedMoment B raw27022step1 raw27022step1Labels = mixedMoment B raw27022step2 raw27022step2Labels := by
      have ha : raw27022step2 = raw27022step1 := by apply Matrix.ext; unfold raw27022step2 raw27022step1; decide +kernel
      have hl : raw27022step1Labels = labelEmbedding9 ∘ raw27022step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27022step1 raw27022step1Labels raw27022step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw27023 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw27023step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27023step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw27023step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27023 raw27023Labels = mixedMoment B node4455 node4455Labels := by
  calc
    mixedMoment B raw27023 raw27023Labels = mixedMoment B raw27023step0 raw27023step0Labels := by
      have ha : raw27023step0 = (fun i j => raw27023 (permutation161 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27023step0 raw27023; decide +kernel
      have hl : raw27023step0Labels = raw27023Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27023 raw27023Labels permutation161 permutation6
    mixedMoment B raw27023step0 raw27023step0Labels = mixedMoment B raw27023step1 raw27023step1Labels := by
      have ha : raw27023step1 = raw27023step0 := by apply Matrix.ext; unfold raw27023step1 raw27023step0; decide +kernel
      have hl : raw27023step0Labels = labelEmbedding9 ∘ raw27023step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27023step0 raw27023step0Labels raw27023step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4455 node4455Labels := by rfl

def raw27024 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw27024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27024step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27024step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27024step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27024step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27024 raw27024Labels = mixedMoment B node4449 node4449Labels := by
  calc
    mixedMoment B raw27024 raw27024Labels = mixedMoment B raw27024step0 raw27024step0Labels := by
      have ha : raw27024step0 = (fun i j => raw27024 (permutation169 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27024step0 raw27024; decide +kernel
      have hl : raw27024step0Labels = raw27024Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27024 raw27024Labels permutation169 permutation6
    mixedMoment B raw27024step0 raw27024step0Labels = mixedMoment B raw27024step1 raw27024step1Labels := by
      have ha : raw27024step1 = raw27024step0 := by apply Matrix.ext; unfold raw27024step1 raw27024step0; decide +kernel
      have hl : raw27024step0Labels = labelEmbedding9 ∘ raw27024step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27024step0 raw27024step0Labels raw27024step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4449 node4449Labels := by rfl

def raw27025 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27025step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27025step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27025step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27025step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27025 raw27025Labels = mixedMoment B node4449 node4449Labels := by
  calc
    mixedMoment B raw27025 raw27025Labels = mixedMoment B raw27025step0 raw27025step0Labels := by
      have ha : raw27025step0 = (fun i j => raw27025 (permutation175 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27025step0 raw27025; decide +kernel
      have hl : raw27025step0Labels = raw27025Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27025 raw27025Labels permutation175 permutation6
    mixedMoment B raw27025step0 raw27025step0Labels = mixedMoment B raw27025step1 raw27025step1Labels := by
      have ha : raw27025step1 = raw27025step0 := by apply Matrix.ext; unfold raw27025step1 raw27025step0; decide +kernel
      have hl : raw27025step0Labels = labelEmbedding9 ∘ raw27025step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27025step0 raw27025step0Labels raw27025step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4449 node4449Labels := by rfl

def raw27026 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw27026step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27026step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27026step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27026step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw27026step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27026 raw27026Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw27026 raw27026Labels = mixedMoment B raw27026step0 raw27026step0Labels := by
      have ha : raw27026step0 = (fun i j => raw27026 (permutation240 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27026step0 raw27026; decide +kernel
      have hl : raw27026step0Labels = raw27026Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27026 raw27026Labels permutation240 permutation4
    mixedMoment B raw27026step0 raw27026step0Labels = mixedMoment B raw27026step1 raw27026step1Labels := by
      have ha : raw27026step1 = -raw27026step0 := by apply Matrix.ext; change ∀ i j, raw27026step1 i j = -(raw27026step0 i j); unfold raw27026step1 raw27026step0; decide +kernel
      have hl : raw27026step1Labels = raw27026step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27026step1 raw27026step1Labels = mixedMoment B raw27026step2 raw27026step2Labels := by
      have ha : raw27026step2 = raw27026step1 := by apply Matrix.ext; unfold raw27026step2 raw27026step1; decide +kernel
      have hl : raw27026step1Labels = labelEmbedding7 ∘ raw27026step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27026step1 raw27026step1Labels raw27026step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4249 node4249Labels := by rfl

def raw27027 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27027step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27027step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27027step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27027 raw27027Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw27027 raw27027Labels = mixedMoment B raw27027step0 raw27027step0Labels := by
      have hz : ∀ j, raw27027 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27027step0 = (fun i j => raw27027 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27027step0 raw27027; decide +kernel
      have hl : raw27027step0Labels = raw27027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27027 raw27027Labels permutation265 hz
    mixedMoment B raw27027step0 raw27027step0Labels = mixedMoment B raw27027step1 raw27027step1Labels := by
      have ha : raw27027step1 = (fun i j => raw27027step0 (permutation48 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27027step1 raw27027step0; decide +kernel
      have hl : raw27027step1Labels = raw27027step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27027step0 raw27027step0Labels permutation48 permutation6
    mixedMoment B raw27027step1 raw27027step1Labels = mixedMoment B raw27027step2 raw27027step2Labels := by
      have ha : raw27027step2 = raw27027step1 := by apply Matrix.ext; unfold raw27027step2 raw27027step1; decide +kernel
      have hl : raw27027step1Labels = labelEmbedding9 ∘ raw27027step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27027step1 raw27027step1Labels raw27027step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw27028 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw27028step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27028step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw27028step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27028 raw27028Labels = mixedMoment B node4455 node4455Labels := by
  calc
    mixedMoment B raw27028 raw27028Labels = mixedMoment B raw27028step0 raw27028step0Labels := by
      have ha : raw27028step0 = (fun i j => raw27028 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27028step0 raw27028; decide +kernel
      have hl : raw27028step0Labels = raw27028Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27028 raw27028Labels permutation155 permutation6
    mixedMoment B raw27028step0 raw27028step0Labels = mixedMoment B raw27028step1 raw27028step1Labels := by
      have ha : raw27028step1 = raw27028step0 := by apply Matrix.ext; unfold raw27028step1 raw27028step0; decide +kernel
      have hl : raw27028step0Labels = labelEmbedding9 ∘ raw27028step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27028step0 raw27028step0Labels raw27028step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4455 node4455Labels := by rfl

def raw27029 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw27029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27029step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27029step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27029step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27029 raw27029Labels = mixedMoment B node4449 node4449Labels := by
  calc
    mixedMoment B raw27029 raw27029Labels = mixedMoment B raw27029step0 raw27029step0Labels := by
      have ha : raw27029step0 = (fun i j => raw27029 (permutation168 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27029step0 raw27029; decide +kernel
      have hl : raw27029step0Labels = raw27029Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27029 raw27029Labels permutation168 permutation6
    mixedMoment B raw27029step0 raw27029step0Labels = mixedMoment B raw27029step1 raw27029step1Labels := by
      have ha : raw27029step1 = raw27029step0 := by apply Matrix.ext; unfold raw27029step1 raw27029step0; decide +kernel
      have hl : raw27029step0Labels = labelEmbedding9 ∘ raw27029step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27029step0 raw27029step0Labels raw27029step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4449 node4449Labels := by rfl

def raw27030 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27030step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27030step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27030 raw27030Labels = mixedMoment B node4449 node4449Labels := by
  calc
    mixedMoment B raw27030 raw27030Labels = mixedMoment B raw27030step0 raw27030step0Labels := by
      have ha : raw27030step0 = (fun i j => raw27030 (permutation174 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27030step0 raw27030; decide +kernel
      have hl : raw27030step0Labels = raw27030Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27030 raw27030Labels permutation174 permutation6
    mixedMoment B raw27030step0 raw27030step0Labels = mixedMoment B raw27030step1 raw27030step1Labels := by
      have ha : raw27030step1 = raw27030step0 := by apply Matrix.ext; unfold raw27030step1 raw27030step0; decide +kernel
      have hl : raw27030step0Labels = labelEmbedding9 ∘ raw27030step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27030step0 raw27030step0Labels raw27030step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4449 node4449Labels := by rfl

def raw27031 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw27031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27031step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27031step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27031step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27031step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27031step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27031 raw27031Labels = mixedMoment B node4263 node4263Labels := by
  calc
    mixedMoment B raw27031 raw27031Labels = mixedMoment B raw27031step0 raw27031step0Labels := by
      have ha : raw27031step0 = (fun i j => raw27031 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27031step0 raw27031; decide +kernel
      have hl : raw27031step0Labels = raw27031Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27031 raw27031Labels permutation246 permutation4
    mixedMoment B raw27031step0 raw27031step0Labels = mixedMoment B raw27031step1 raw27031step1Labels := by
      have ha : raw27031step1 = -raw27031step0 := by apply Matrix.ext; change ∀ i j, raw27031step1 i j = -(raw27031step0 i j); unfold raw27031step1 raw27031step0; decide +kernel
      have hl : raw27031step1Labels = raw27031step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27031step1 raw27031step1Labels = mixedMoment B raw27031step2 raw27031step2Labels := by
      have ha : raw27031step2 = raw27031step1 := by apply Matrix.ext; unfold raw27031step2 raw27031step1; decide +kernel
      have hl : raw27031step1Labels = labelEmbedding7 ∘ raw27031step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27031step1 raw27031step1Labels raw27031step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4263 node4263Labels := by rfl

def raw27032 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw27032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27032step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27032step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27032step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27032step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27032 raw27032Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw27032 raw27032Labels = mixedMoment B raw27032step0 raw27032step0Labels := by
      have ha : raw27032step0 = (fun i j => raw27032 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27032step0 raw27032; decide +kernel
      have hl : raw27032step0Labels = raw27032Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27032 raw27032Labels permutation156 permutation6
    mixedMoment B raw27032step0 raw27032step0Labels = mixedMoment B raw27032step1 raw27032step1Labels := by
      have ha : raw27032step1 = raw27032step0 := by apply Matrix.ext; unfold raw27032step1 raw27032step0; decide +kernel
      have hl : raw27032step0Labels = labelEmbedding9 ∘ raw27032step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27032step0 raw27032step0Labels raw27032step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw27033 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw27033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27033step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27033step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27033step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27033step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27033 raw27033Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw27033 raw27033Labels = mixedMoment B raw27033step0 raw27033step0Labels := by
      have ha : raw27033step0 = (fun i j => raw27033 (permutation162 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27033step0 raw27033; decide +kernel
      have hl : raw27033step0Labels = raw27033Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27033 raw27033Labels permutation162 permutation6
    mixedMoment B raw27033step0 raw27033step0Labels = mixedMoment B raw27033step1 raw27033step1Labels := by
      have ha : raw27033step1 = raw27033step0 := by apply Matrix.ext; unfold raw27033step1 raw27033step0; decide +kernel
      have hl : raw27033step0Labels = labelEmbedding9 ∘ raw27033step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27033step0 raw27033step0Labels raw27033step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw27034 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw27034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27034step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27034step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27034 raw27034Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw27034 raw27034Labels = mixedMoment B raw27034step0 raw27034step0Labels := by
      have ha : raw27034step0 = (fun i j => raw27034 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27034step0 raw27034; decide +kernel
      have hl : raw27034step0Labels = raw27034Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27034 raw27034Labels permutation170 permutation6
    mixedMoment B raw27034step0 raw27034step0Labels = mixedMoment B raw27034step1 raw27034step1Labels := by
      have ha : raw27034step1 = raw27034step0 := by apply Matrix.ext; unfold raw27034step1 raw27034step0; decide +kernel
      have hl : raw27034step0Labels = labelEmbedding9 ∘ raw27034step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27034step0 raw27034step0Labels raw27034step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4451 node4451Labels := by rfl

def raw27035 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw27035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw27035step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27035step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw27035step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27035step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27035 raw27035Labels = mixedMoment B node4263 node4263Labels := by
  calc
    mixedMoment B raw27035 raw27035Labels = mixedMoment B raw27035step0 raw27035step0Labels := by
      have ha : raw27035step0 = (fun i j => raw27035 (permutation224 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27035step0 raw27035; decide +kernel
      have hl : raw27035step0Labels = raw27035Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27035 raw27035Labels permutation224 permutation4
    mixedMoment B raw27035step0 raw27035step0Labels = mixedMoment B raw27035step1 raw27035step1Labels := by
      have ha : raw27035step1 = -raw27035step0 := by apply Matrix.ext; change ∀ i j, raw27035step1 i j = -(raw27035step0 i j); unfold raw27035step1 raw27035step0; decide +kernel
      have hl : raw27035step1Labels = raw27035step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27035step1 raw27035step1Labels = mixedMoment B raw27035step2 raw27035step2Labels := by
      have ha : raw27035step2 = raw27035step1 := by apply Matrix.ext; unfold raw27035step2 raw27035step1; decide +kernel
      have hl : raw27035step1Labels = labelEmbedding7 ∘ raw27035step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27035step1 raw27035step1Labels raw27035step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4263 node4263Labels := by rfl

def raw27036 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw27036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw27036step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27036step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27036step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27036 raw27036Labels = mixedMoment B node4497 node4497Labels := by
  calc
    mixedMoment B raw27036 raw27036Labels = mixedMoment B raw27036step0 raw27036step0Labels := by
      have hz : ∀ j, raw27036 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27036step0 = (fun i j => raw27036 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27036step0 raw27036; decide +kernel
      have hl : raw27036step0Labels = raw27036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27036 raw27036Labels permutation265 hz
    mixedMoment B raw27036step0 raw27036step0Labels = mixedMoment B raw27036step1 raw27036step1Labels := by
      have ha : raw27036step1 = (fun i j => raw27036step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27036step1 raw27036step0; decide +kernel
      have hl : raw27036step1Labels = raw27036step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27036step0 raw27036step0Labels permutation44 permutation6
    mixedMoment B raw27036step1 raw27036step1Labels = mixedMoment B raw27036step2 raw27036step2Labels := by
      have ha : raw27036step2 = raw27036step1 := by apply Matrix.ext; unfold raw27036step2 raw27036step1; decide +kernel
      have hl : raw27036step1Labels = labelEmbedding9 ∘ raw27036step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27036step1 raw27036step1Labels raw27036step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4497 node4497Labels := by rfl

def raw27037 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw27037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27037step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27037step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27037 raw27037Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw27037 raw27037Labels = mixedMoment B raw27037step0 raw27037step0Labels := by
      have ha : raw27037step0 = (fun i j => raw27037 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27037step0 raw27037; decide +kernel
      have hl : raw27037step0Labels = raw27037Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27037 raw27037Labels permutation154 permutation6
    mixedMoment B raw27037step0 raw27037step0Labels = mixedMoment B raw27037step1 raw27037step1Labels := by
      have ha : raw27037step1 = raw27037step0 := by apply Matrix.ext; unfold raw27037step1 raw27037step0; decide +kernel
      have hl : raw27037step0Labels = labelEmbedding9 ∘ raw27037step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27037step0 raw27037step0Labels raw27037step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw27038 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw27038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27038step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27038step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27038 raw27038Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw27038 raw27038Labels = mixedMoment B raw27038step0 raw27038step0Labels := by
      have ha : raw27038step0 = (fun i j => raw27038 (permutation160 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27038step0 raw27038; decide +kernel
      have hl : raw27038step0Labels = raw27038Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27038 raw27038Labels permutation160 permutation6
    mixedMoment B raw27038step0 raw27038step0Labels = mixedMoment B raw27038step1 raw27038step1Labels := by
      have ha : raw27038step1 = raw27038step0 := by apply Matrix.ext; unfold raw27038step1 raw27038step0; decide +kernel
      have hl : raw27038step0Labels = labelEmbedding9 ∘ raw27038step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27038step0 raw27038step0Labels raw27038step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw27039 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw27039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27039step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw27039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw27039step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27039 raw27039Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw27039 raw27039Labels = mixedMoment B raw27039step0 raw27039step0Labels := by
      have ha : raw27039step0 = (fun i j => raw27039 (permutation164 i) (permutation6 j)) := by apply Matrix.ext; unfold raw27039step0 raw27039; decide +kernel
      have hl : raw27039step0Labels = raw27039Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27039 raw27039Labels permutation164 permutation6
    mixedMoment B raw27039step0 raw27039step0Labels = mixedMoment B raw27039step1 raw27039step1Labels := by
      have ha : raw27039step1 = raw27039step0 := by apply Matrix.ext; unfold raw27039step1 raw27039step0; decide +kernel
      have hl : raw27039step0Labels = labelEmbedding9 ∘ raw27039step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27039step0 raw27039step0Labels raw27039step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4451 node4451Labels := by rfl

def raw27040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw27040Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw27040step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27040step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27040 raw27040Labels = mixedMoment B node1070 node1070Labels := by
  calc
    mixedMoment B raw27040 raw27040Labels = mixedMoment B raw27040step0 raw27040step0Labels := by
      have hz : ∀ j, raw27040 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27040step0 = (fun i j => raw27040 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27040step0 raw27040; decide +kernel
      have hl : raw27040step0Labels = raw27040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27040 raw27040Labels permutation265 hz
    mixedMoment B raw27040step0 raw27040step0Labels = mixedMoment B raw27040step1 raw27040step1Labels := by
      have ha : raw27040step1 = (fun i j => raw27040step0 (permutation55 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27040step1 raw27040step0; decide +kernel
      have hl : raw27040step1Labels = raw27040step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27040step0 raw27040step0Labels permutation55 permutation2
    _ = mixedMoment B node1070 node1070Labels := by rfl

def raw27041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw27041Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27041 raw27041Labels = mixedMoment B node2043 node2043Labels := by
  calc
    mixedMoment B raw27041 raw27041Labels = mixedMoment B raw27041step0 raw27041step0Labels := by
      have ha : raw27041step0 = (fun i j => raw27041 (permutation175 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27041step0 raw27041; decide +kernel
      have hl : raw27041step0Labels = raw27041Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27041 raw27041Labels permutation175 permutation2
    _ = mixedMoment B node2043 node2043Labels := by rfl

def raw27042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw27042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw27042step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-2, 1, 1]]
def raw27042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27042step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw27042step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27042 raw27042Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw27042 raw27042Labels = mixedMoment B raw27042step0 raw27042step0Labels := by
      have hz : ∀ j, raw27042 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27042step0 = (fun i j => raw27042 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27042step0 raw27042; decide +kernel
      have hl : raw27042step0Labels = raw27042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27042 raw27042Labels permutation265 hz
    mixedMoment B raw27042step0 raw27042step0Labels = mixedMoment B raw27042step1 raw27042step1Labels := by
      have ha : raw27042step1 = (fun i j => raw27042step0 (permutation62 i) (permutation4 j)) := by apply Matrix.ext; unfold raw27042step1 raw27042step0; decide +kernel
      have hl : raw27042step1Labels = raw27042step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27042step0 raw27042step0Labels permutation62 permutation4
    mixedMoment B raw27042step1 raw27042step1Labels = mixedMoment B raw27042step2 raw27042step2Labels := by
      have ha : raw27042step2 = -raw27042step1 := by apply Matrix.ext; change ∀ i j, raw27042step2 i j = -(raw27042step1 i j); unfold raw27042step2 raw27042step1; decide +kernel
      have hl : raw27042step2Labels = raw27042step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw27043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw27043Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1]]
def raw27043step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw27043step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27043 raw27043Labels = mixedMoment B node2259 node2259Labels := by
  calc
    mixedMoment B raw27043 raw27043Labels = mixedMoment B raw27043step0 raw27043step0Labels := by
      have hz : ∀ j, raw27043 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27043step0 = (fun i j => raw27043 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27043step0 raw27043; decide +kernel
      have hl : raw27043step0Labels = raw27043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27043 raw27043Labels permutation265 hz
    mixedMoment B raw27043step0 raw27043step0Labels = mixedMoment B raw27043step1 raw27043step1Labels := by
      have ha : raw27043step1 = (fun i j => raw27043step0 (permutation43 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27043step1 raw27043step0; decide +kernel
      have hl : raw27043step1Labels = raw27043step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27043step0 raw27043step0Labels permutation43 permutation2
    _ = mixedMoment B node2259 node2259Labels := by rfl

def raw27044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1]]
def raw27044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw27044step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27044step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw27044step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27044step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw27044step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27044 raw27044Labels = mixedMoment B node2287 node2287Labels := by
  calc
    mixedMoment B raw27044 raw27044Labels = mixedMoment B raw27044step0 raw27044step0Labels := by
      have hz : ∀ j, raw27044 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27044step0 = (fun i j => raw27044 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27044step0 raw27044; decide +kernel
      have hl : raw27044step0Labels = raw27044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27044 raw27044Labels permutation520 hz
    mixedMoment B raw27044step0 raw27044step0Labels = mixedMoment B raw27044step1 raw27044step1Labels := by
      have hz : ∀ j, raw27044step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27044step1 = (fun i j => raw27044step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27044step1 raw27044step0; decide +kernel
      have hl : raw27044step1Labels = raw27044step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27044step0 raw27044step0Labels permutation56 hz
    mixedMoment B raw27044step1 raw27044step1Labels = mixedMoment B raw27044step2 raw27044step2Labels := by
      have ha : raw27044step2 = (fun i j => raw27044step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27044step2 raw27044step1; decide +kernel
      have hl : raw27044step2Labels = raw27044step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27044step1 raw27044step1Labels permutation13 permutation2
    _ = mixedMoment B node2287 node2287Labels := by rfl

def raw27045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1]]
def raw27045Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1]]
def raw27045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw27045step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27045 raw27045Labels = mixedMoment B node2224 node2224Labels := by
  calc
    mixedMoment B raw27045 raw27045Labels = mixedMoment B raw27045step0 raw27045step0Labels := by
      have hz : ∀ j, raw27045 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27045step0 = (fun i j => raw27045 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27045step0 raw27045; decide +kernel
      have hl : raw27045step0Labels = raw27045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27045 raw27045Labels permutation265 hz
    mixedMoment B raw27045step0 raw27045step0Labels = mixedMoment B raw27045step1 raw27045step1Labels := by
      have ha : raw27045step1 = (fun i j => raw27045step0 (permutation55 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27045step1 raw27045step0; decide +kernel
      have hl : raw27045step1Labels = raw27045step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27045step0 raw27045step0Labels permutation55 permutation2
    _ = mixedMoment B node2224 node2224Labels := by rfl

def raw27046 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3], ![1, -1], ![0, 0], ![-1, 1]]
def raw27046Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27046step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![3, -3], ![1, -1], ![-1, 1]]
def raw27046step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27046step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![3, -3], ![1, -1], ![-1, 1]]
def raw27046step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27046step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw27046step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27046 raw27046Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw27046 raw27046Labels = mixedMoment B raw27046step0 raw27046step0Labels := by
      have hz : ∀ j, raw27046 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27046step0 = (fun i j => raw27046 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27046step0 raw27046; decide +kernel
      have hl : raw27046step0Labels = raw27046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27046 raw27046Labels permutation520 hz
    mixedMoment B raw27046step0 raw27046step0Labels = mixedMoment B raw27046step1 raw27046step1Labels := by
      have hz : ∀ j, raw27046step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27046step1 = (fun i j => raw27046step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27046step1 raw27046step0; decide +kernel
      have hl : raw27046step1Labels = raw27046step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27046step0 raw27046step0Labels permutation56 hz
    mixedMoment B raw27046step1 raw27046step1Labels = mixedMoment B raw27046step2 raw27046step2Labels := by
      have ha : raw27046step2 = (fun i j => raw27046step1 (permutation13 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27046step2 raw27046step1; decide +kernel
      have hl : raw27046step2Labels = raw27046step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27046step1 raw27046step1Labels permutation13 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw27047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw27047Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw27047step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27047step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27047 raw27047Labels = mixedMoment B node1071 node1071Labels := by
  calc
    mixedMoment B raw27047 raw27047Labels = mixedMoment B raw27047step0 raw27047step0Labels := by
      have hz : ∀ j, raw27047 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27047step0 = (fun i j => raw27047 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27047step0 raw27047; decide +kernel
      have hl : raw27047step0Labels = raw27047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27047 raw27047Labels permutation265 hz
    mixedMoment B raw27047step0 raw27047step0Labels = mixedMoment B raw27047step1 raw27047step1Labels := by
      have ha : raw27047step1 = (fun i j => raw27047step0 (permutation54 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27047step1 raw27047step0; decide +kernel
      have hl : raw27047step1Labels = raw27047step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27047step0 raw27047step0Labels permutation54 permutation2
    _ = mixedMoment B node1071 node1071Labels := by rfl

def raw27048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw27048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27048step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27048 raw27048Labels = mixedMoment B node2044 node2044Labels := by
  calc
    mixedMoment B raw27048 raw27048Labels = mixedMoment B raw27048step0 raw27048step0Labels := by
      have ha : raw27048step0 = (fun i j => raw27048 (permutation174 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27048step0 raw27048; decide +kernel
      have hl : raw27048step0Labels = raw27048Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27048 raw27048Labels permutation174 permutation2
    _ = mixedMoment B node2044 node2044Labels := by rfl

def raw27049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw27049Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw27049step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw27049step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27049 raw27049Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw27049 raw27049Labels = mixedMoment B raw27049step0 raw27049step0Labels := by
      have hz : ∀ j, raw27049 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27049step0 = (fun i j => raw27049 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27049step0 raw27049; decide +kernel
      have hl : raw27049step0Labels = raw27049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27049 raw27049Labels permutation265 hz
    mixedMoment B raw27049step0 raw27049step0Labels = mixedMoment B raw27049step1 raw27049step1Labels := by
      have ha : raw27049step1 = (fun i j => raw27049step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27049step1 raw27049step0; decide +kernel
      have hl : raw27049step1Labels = raw27049step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27049step0 raw27049step0Labels permutation37 permutation2
    _ = mixedMoment B node2274 node2274Labels := by rfl

def raw27050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1]]
def raw27050Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1]]
def raw27050step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw27050step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27050 raw27050Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw27050 raw27050Labels = mixedMoment B raw27050step0 raw27050step0Labels := by
      have hz : ∀ j, raw27050 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27050step0 = (fun i j => raw27050 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27050step0 raw27050; decide +kernel
      have hl : raw27050step0Labels = raw27050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27050 raw27050Labels permutation265 hz
    mixedMoment B raw27050step0 raw27050step0Labels = mixedMoment B raw27050step1 raw27050step1Labels := by
      have ha : raw27050step1 = (fun i j => raw27050step0 (permutation43 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27050step1 raw27050step0; decide +kernel
      have hl : raw27050step1Labels = raw27050step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27050step0 raw27050step0Labels permutation43 permutation2
    _ = mixedMoment B node2274 node2274Labels := by rfl

def raw27051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![1, -2, 1]]
def raw27051Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw27051step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27051step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw27051step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27051step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw27051step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27051 raw27051Labels = mixedMoment B node2288 node2288Labels := by
  calc
    mixedMoment B raw27051 raw27051Labels = mixedMoment B raw27051step0 raw27051step0Labels := by
      have hz : ∀ j, raw27051 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27051step0 = (fun i j => raw27051 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27051step0 raw27051; decide +kernel
      have hl : raw27051step0Labels = raw27051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27051 raw27051Labels permutation520 hz
    mixedMoment B raw27051step0 raw27051step0Labels = mixedMoment B raw27051step1 raw27051step1Labels := by
      have hz : ∀ j, raw27051step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27051step1 = (fun i j => raw27051step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27051step1 raw27051step0; decide +kernel
      have hl : raw27051step1Labels = raw27051step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27051step0 raw27051step0Labels permutation56 hz
    mixedMoment B raw27051step1 raw27051step1Labels = mixedMoment B raw27051step2 raw27051step2Labels := by
      have ha : raw27051step2 = (fun i j => raw27051step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27051step2 raw27051step1; decide +kernel
      have hl : raw27051step2Labels = raw27051step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27051step1 raw27051step1Labels permutation12 permutation2
    _ = mixedMoment B node2288 node2288Labels := by rfl

def raw27052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![0, -1, 1]]
def raw27052Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0], ![0, -1, 1]]
def raw27052step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw27052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27052 raw27052Labels = mixedMoment B node2225 node2225Labels := by
  calc
    mixedMoment B raw27052 raw27052Labels = mixedMoment B raw27052step0 raw27052step0Labels := by
      have hz : ∀ j, raw27052 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27052step0 = (fun i j => raw27052 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27052step0 raw27052; decide +kernel
      have hl : raw27052step0Labels = raw27052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27052 raw27052Labels permutation265 hz
    mixedMoment B raw27052step0 raw27052step0Labels = mixedMoment B raw27052step1 raw27052step1Labels := by
      have ha : raw27052step1 = (fun i j => raw27052step0 (permutation54 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27052step1 raw27052step0; decide +kernel
      have hl : raw27052step1Labels = raw27052step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27052step0 raw27052step0Labels permutation54 permutation2
    _ = mixedMoment B node2225 node2225Labels := by rfl

def raw27053 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![2, -2], ![0, 0], ![-1, 1]]
def raw27053Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27053step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![2, -2], ![-1, 1]]
def raw27053step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27053step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![2, -2], ![-1, 1]]
def raw27053step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27053step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw27053step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27053 raw27053Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw27053 raw27053Labels = mixedMoment B raw27053step0 raw27053step0Labels := by
      have hz : ∀ j, raw27053 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27053step0 = (fun i j => raw27053 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27053step0 raw27053; decide +kernel
      have hl : raw27053step0Labels = raw27053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27053 raw27053Labels permutation520 hz
    mixedMoment B raw27053step0 raw27053step0Labels = mixedMoment B raw27053step1 raw27053step1Labels := by
      have hz : ∀ j, raw27053step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27053step1 = (fun i j => raw27053step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27053step1 raw27053step0; decide +kernel
      have hl : raw27053step1Labels = raw27053step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27053step0 raw27053step0Labels permutation56 hz
    mixedMoment B raw27053step1 raw27053step1Labels = mixedMoment B raw27053step2 raw27053step2Labels := by
      have ha : raw27053step2 = (fun i j => raw27053step1 (permutation12 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27053step2 raw27053step1; decide +kernel
      have hl : raw27053step2Labels = raw27053step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27053step1 raw27053step1Labels permutation12 permutation0
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw27054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw27054Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw27054step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27054 raw27054Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw27054 raw27054Labels = mixedMoment B raw27054step0 raw27054step0Labels := by
      have hz : ∀ j, raw27054 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27054step0 = (fun i j => raw27054 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27054step0 raw27054; decide +kernel
      have hl : raw27054step0Labels = raw27054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27054 raw27054Labels permutation265 hz
    mixedMoment B raw27054step0 raw27054step0Labels = mixedMoment B raw27054step1 raw27054step1Labels := by
      have ha : raw27054step1 = (fun i j => raw27054step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27054step1 raw27054step0; decide +kernel
      have hl : raw27054step1Labels = raw27054step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27054step0 raw27054step0Labels permutation53 permutation2
    _ = mixedMoment B node1073 node1073Labels := by rfl

def raw27055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw27055Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27055 raw27055Labels = mixedMoment B node2046 node2046Labels := by
  calc
    mixedMoment B raw27055 raw27055Labels = mixedMoment B raw27055step0 raw27055step0Labels := by
      have ha : raw27055step0 = (fun i j => raw27055 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27055step0 raw27055; decide +kernel
      have hl : raw27055step0Labels = raw27055Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27055 raw27055Labels permutation173 permutation2
    _ = mixedMoment B node2046 node2046Labels := by rfl

def raw27056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw27056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw27056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw27056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27056 raw27056Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw27056 raw27056Labels = mixedMoment B raw27056step0 raw27056step0Labels := by
      have hz : ∀ j, raw27056 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27056step0 = (fun i j => raw27056 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27056step0 raw27056; decide +kernel
      have hl : raw27056step0Labels = raw27056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27056 raw27056Labels permutation265 hz
    mixedMoment B raw27056step0 raw27056step0Labels = mixedMoment B raw27056step1 raw27056step1Labels := by
      have ha : raw27056step1 = (fun i j => raw27056step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27056step1 raw27056step0; decide +kernel
      have hl : raw27056step1Labels = raw27056step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27056step0 raw27056step0Labels permutation36 permutation2
    _ = mixedMoment B node2275 node2275Labels := by rfl

def raw27057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw27057Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw27057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw27057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27057 raw27057Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw27057 raw27057Labels = mixedMoment B raw27057step0 raw27057step0Labels := by
      have hz : ∀ j, raw27057 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27057step0 = (fun i j => raw27057 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27057step0 raw27057; decide +kernel
      have hl : raw27057step0Labels = raw27057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27057 raw27057Labels permutation265 hz
    mixedMoment B raw27057step0 raw27057step0Labels = mixedMoment B raw27057step1 raw27057step1Labels := by
      have ha : raw27057step1 = (fun i j => raw27057step0 (permutation43 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27057step1 raw27057step0; decide +kernel
      have hl : raw27057step1Labels = raw27057step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27057step0 raw27057step0Labels permutation43 permutation2
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw27058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw27058Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw27058step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw27058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27058 raw27058Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw27058 raw27058Labels = mixedMoment B raw27058step0 raw27058step0Labels := by
      have hz : ∀ j, raw27058 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27058step0 = (fun i j => raw27058 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27058step0 raw27058; decide +kernel
      have hl : raw27058step0Labels = raw27058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27058 raw27058Labels permutation265 hz
    mixedMoment B raw27058step0 raw27058step0Labels = mixedMoment B raw27058step1 raw27058step1Labels := by
      have ha : raw27058step1 = (fun i j => raw27058step0 (permutation49 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27058step1 raw27058step0; decide +kernel
      have hl : raw27058step1Labels = raw27058step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27058step0 raw27058step0Labels permutation49 permutation2
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw27059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw27059Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw27059step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw27059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27059 raw27059Labels = mixedMoment B node2227 node2227Labels := by
  calc
    mixedMoment B raw27059 raw27059Labels = mixedMoment B raw27059step0 raw27059step0Labels := by
      have hz : ∀ j, raw27059 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27059step0 = (fun i j => raw27059 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27059step0 raw27059; decide +kernel
      have hl : raw27059step0Labels = raw27059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27059 raw27059Labels permutation265 hz
    mixedMoment B raw27059step0 raw27059step0Labels = mixedMoment B raw27059step1 raw27059step1Labels := by
      have ha : raw27059step1 = (fun i j => raw27059step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27059step1 raw27059step0; decide +kernel
      have hl : raw27059step1Labels = raw27059step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27059step0 raw27059step0Labels permutation53 permutation2
    _ = mixedMoment B node2227 node2227Labels := by rfl

def raw27060 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![2, -2], ![1, -1], ![1, -1], ![-1, 1]]
def raw27060Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27060step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1], ![1, -1], ![-1, 1]]
def raw27060step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw27060step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw27060step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical27060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27060 raw27060Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw27060 raw27060Labels = mixedMoment B raw27060step0 raw27060step0Labels := by
      have hz : ∀ j, raw27060 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27060step0 = (fun i j => raw27060 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27060step0 raw27060; decide +kernel
      have hl : raw27060step0Labels = raw27060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27060 raw27060Labels permutation265 hz
    mixedMoment B raw27060step0 raw27060step0Labels = mixedMoment B raw27060step1 raw27060step1Labels := by
      have ha : raw27060step1 = (fun i j => raw27060step0 (permutation53 i) (permutation0 j)) := by apply Matrix.ext; unfold raw27060step1 raw27060step0; decide +kernel
      have hl : raw27060step1Labels = raw27060step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27060step0 raw27060step0Labels permutation53 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw27061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27061step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27061 raw27061Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw27061 raw27061Labels = mixedMoment B raw27061step0 raw27061step0Labels := by
      have ha : raw27061step0 = (fun i j => raw27061 (permutation169 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27061step0 raw27061; decide +kernel
      have hl : raw27061step0Labels = raw27061Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27061 raw27061Labels permutation169 permutation2
    _ = mixedMoment B node4831 node4831Labels := by rfl

def raw27062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27062step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27062step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27062step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27062step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27062step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27062step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27062 raw27062Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw27062 raw27062Labels = mixedMoment B raw27062step0 raw27062step0Labels := by
      have hz : ∀ j, raw27062 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27062step0 = (fun i j => raw27062 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27062step0 raw27062; decide +kernel
      have hl : raw27062step0Labels = raw27062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27062 raw27062Labels permutation265 hz
    mixedMoment B raw27062step0 raw27062step0Labels = mixedMoment B raw27062step1 raw27062step1Labels := by
      have ha : raw27062step1 = (fun i j => raw27062step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27062step1 raw27062step0; decide +kernel
      have hl : raw27062step1Labels = raw27062step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27062step0 raw27062step0Labels permutation49 permutation7
    mixedMoment B raw27062step1 raw27062step1Labels = mixedMoment B raw27062step2 raw27062step2Labels := by
      have ha : raw27062step2 = -raw27062step1 := by apply Matrix.ext; change ∀ i j, raw27062step2 i j = -(raw27062step1 i j); unfold raw27062step2 raw27062step1; decide +kernel
      have hl : raw27062step2Labels = raw27062step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27062step2 raw27062step2Labels = mixedMoment B raw27062step3 raw27062step3Labels := by
      have ha : raw27062step3 = raw27062step2 := by apply Matrix.ext; unfold raw27062step3 raw27062step2; decide +kernel
      have hl : raw27062step2Labels = labelEmbedding10 ∘ raw27062step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27062step2 raw27062step2Labels raw27062step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw27063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27063step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw27063step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27063step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw27063step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27063step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw27063step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27063 raw27063Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw27063 raw27063Labels = mixedMoment B raw27063step0 raw27063step0Labels := by
      have hz : ∀ j, raw27063 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27063step0 = (fun i j => raw27063 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27063step0 raw27063; decide +kernel
      have hl : raw27063step0Labels = raw27063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27063 raw27063Labels permutation265 hz
    mixedMoment B raw27063step0 raw27063step0Labels = mixedMoment B raw27063step1 raw27063step1Labels := by
      have ha : raw27063step1 = (fun i j => raw27063step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27063step1 raw27063step0; decide +kernel
      have hl : raw27063step1Labels = raw27063step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27063step0 raw27063step0Labels permutation49 permutation7
    mixedMoment B raw27063step1 raw27063step1Labels = mixedMoment B raw27063step2 raw27063step2Labels := by
      have ha : raw27063step2 = -raw27063step1 := by apply Matrix.ext; change ∀ i j, raw27063step2 i j = -(raw27063step1 i j); unfold raw27063step2 raw27063step1; decide +kernel
      have hl : raw27063step2Labels = raw27063step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27063step2 raw27063step2Labels = mixedMoment B raw27063step3 raw27063step3Labels := by
      have ha : raw27063step3 = raw27063step2 := by apply Matrix.ext; unfold raw27063step3 raw27063step2; decide +kernel
      have hl : raw27063step2Labels = labelEmbedding10 ∘ raw27063step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27063step2 raw27063step2Labels raw27063step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw27064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw27064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27064step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27064step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27064step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27064step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27064step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27064step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27064step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27064step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27064 raw27064Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw27064 raw27064Labels = mixedMoment B raw27064step0 raw27064step0Labels := by
      have hz : ∀ j, raw27064 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27064step0 = (fun i j => raw27064 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27064step0 raw27064; decide +kernel
      have hl : raw27064step0Labels = raw27064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27064 raw27064Labels permutation520 hz
    mixedMoment B raw27064step0 raw27064step0Labels = mixedMoment B raw27064step1 raw27064step1Labels := by
      have hz : ∀ j, raw27064step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27064step1 = (fun i j => raw27064step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27064step1 raw27064step0; decide +kernel
      have hl : raw27064step1Labels = raw27064step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27064step0 raw27064step0Labels permutation56 hz
    mixedMoment B raw27064step1 raw27064step1Labels = mixedMoment B raw27064step2 raw27064step2Labels := by
      have ha : raw27064step2 = (fun i j => raw27064step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27064step2 raw27064step1; decide +kernel
      have hl : raw27064step2Labels = raw27064step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27064step1 raw27064step1Labels permutation13 permutation7
    mixedMoment B raw27064step2 raw27064step2Labels = mixedMoment B raw27064step3 raw27064step3Labels := by
      have ha : raw27064step3 = -raw27064step2 := by apply Matrix.ext; change ∀ i j, raw27064step3 i j = -(raw27064step2 i j); unfold raw27064step3 raw27064step2; decide +kernel
      have hl : raw27064step3Labels = raw27064step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27064step3 raw27064step3Labels = mixedMoment B raw27064step4 raw27064step4Labels := by
      have ha : raw27064step4 = raw27064step3 := by apply Matrix.ext; unfold raw27064step4 raw27064step3; decide +kernel
      have hl : raw27064step3Labels = labelEmbedding10 ∘ raw27064step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27064step3 raw27064step3Labels raw27064step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw27065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw27065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27065step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27065step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27065step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27065step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27065step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27065step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27065step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw27065step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27065step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27065 raw27065Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw27065 raw27065Labels = mixedMoment B raw27065step0 raw27065step0Labels := by
      have hz : ∀ j, raw27065 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27065step0 = (fun i j => raw27065 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27065step0 raw27065; decide +kernel
      have hl : raw27065step0Labels = raw27065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27065 raw27065Labels permutation590 hz
    mixedMoment B raw27065step0 raw27065step0Labels = mixedMoment B raw27065step1 raw27065step1Labels := by
      have hz : ∀ j, raw27065step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27065step1 = (fun i j => raw27065step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27065step1 raw27065step0; decide +kernel
      have hl : raw27065step1Labels = raw27065step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27065step0 raw27065step0Labels permutation56 hz
    mixedMoment B raw27065step1 raw27065step1Labels = mixedMoment B raw27065step2 raw27065step2Labels := by
      have ha : raw27065step2 = (fun i j => raw27065step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27065step2 raw27065step1; decide +kernel
      have hl : raw27065step2Labels = raw27065step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27065step1 raw27065step1Labels permutation13 permutation7
    mixedMoment B raw27065step2 raw27065step2Labels = mixedMoment B raw27065step3 raw27065step3Labels := by
      have ha : raw27065step3 = -raw27065step2 := by apply Matrix.ext; change ∀ i j, raw27065step3 i j = -(raw27065step2 i j); unfold raw27065step3 raw27065step2; decide +kernel
      have hl : raw27065step3Labels = raw27065step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27065step3 raw27065step3Labels = mixedMoment B raw27065step4 raw27065step4Labels := by
      have ha : raw27065step4 = raw27065step3 := by apply Matrix.ext; unfold raw27065step4 raw27065step3; decide +kernel
      have hl : raw27065step3Labels = labelEmbedding10 ∘ raw27065step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27065step3 raw27065step3Labels raw27065step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw27066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27066step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27066 raw27066Labels = mixedMoment B node4169 node4169Labels := by
  calc
    mixedMoment B raw27066 raw27066Labels = mixedMoment B raw27066step0 raw27066step0Labels := by
      have ha : raw27066step0 = (fun i j => raw27066 (permutation169 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27066step0 raw27066; decide +kernel
      have hl : raw27066step0Labels = raw27066Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27066 raw27066Labels permutation169 permutation2
    _ = mixedMoment B node4169 node4169Labels := by rfl

def raw27067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw27067step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27067 raw27067Labels = mixedMoment B node4473 node4473Labels := by
  calc
    mixedMoment B raw27067 raw27067Labels = mixedMoment B raw27067step0 raw27067step0Labels := by
      have ha : raw27067step0 = (fun i j => raw27067 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27067step0 raw27067; decide +kernel
      have hl : raw27067step0Labels = raw27067Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27067 raw27067Labels permutation179 permutation2
    _ = mixedMoment B node4473 node4473Labels := by rfl

def raw27068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw27068step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27068 raw27068Labels = mixedMoment B node4455 node4455Labels := by
  calc
    mixedMoment B raw27068 raw27068Labels = mixedMoment B raw27068step0 raw27068step0Labels := by
      have ha : raw27068step0 = (fun i j => raw27068 (permutation203 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27068step0 raw27068; decide +kernel
      have hl : raw27068step0Labels = raw27068Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27068 raw27068Labels permutation203 permutation2
    _ = mixedMoment B node4455 node4455Labels := by rfl

def raw27069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw27069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27069step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27069step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27069 raw27069Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw27069 raw27069Labels = mixedMoment B raw27069step0 raw27069step0Labels := by
      have hz : ∀ j, raw27069 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27069step0 = (fun i j => raw27069 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27069step0 raw27069; decide +kernel
      have hl : raw27069step0Labels = raw27069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27069 raw27069Labels permutation520 hz
    mixedMoment B raw27069step0 raw27069step0Labels = mixedMoment B raw27069step1 raw27069step1Labels := by
      have ha : raw27069step1 = (fun i j => raw27069step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27069step1 raw27069step0; decide +kernel
      have hl : raw27069step1Labels = raw27069step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27069step0 raw27069step0Labels permutation37 permutation2
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw27070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw27070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27070step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27070step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27070 raw27070Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw27070 raw27070Labels = mixedMoment B raw27070step0 raw27070step0Labels := by
      have hz : ∀ j, raw27070 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27070step0 = (fun i j => raw27070 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27070step0 raw27070; decide +kernel
      have hl : raw27070step0Labels = raw27070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27070 raw27070Labels permutation590 hz
    mixedMoment B raw27070step0 raw27070step0Labels = mixedMoment B raw27070step1 raw27070step1Labels := by
      have ha : raw27070step1 = (fun i j => raw27070step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27070step1 raw27070step0; decide +kernel
      have hl : raw27070step1Labels = raw27070step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27070step0 raw27070step0Labels permutation37 permutation2
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw27071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27071step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27071step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27071 raw27071Labels = mixedMoment B node4172 node4172Labels := by
  calc
    mixedMoment B raw27071 raw27071Labels = mixedMoment B raw27071step0 raw27071step0Labels := by
      have hz : ∀ j, raw27071 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27071step0 = (fun i j => raw27071 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27071step0 raw27071; decide +kernel
      have hl : raw27071step0Labels = raw27071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27071 raw27071Labels permutation265 hz
    mixedMoment B raw27071step0 raw27071step0Labels = mixedMoment B raw27071step1 raw27071step1Labels := by
      have ha : raw27071step1 = (fun i j => raw27071step0 (permutation49 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27071step1 raw27071step0; decide +kernel
      have hl : raw27071step1Labels = raw27071step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27071step0 raw27071step0Labels permutation49 permutation2
    _ = mixedMoment B node4172 node4172Labels := by rfl

def raw27072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27072step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27072 raw27072Labels = mixedMoment B node4341 node4341Labels := by
  calc
    mixedMoment B raw27072 raw27072Labels = mixedMoment B raw27072step0 raw27072step0Labels := by
      have ha : raw27072step0 = (fun i j => raw27072 (permutation169 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27072step0 raw27072; decide +kernel
      have hl : raw27072step0Labels = raw27072Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27072 raw27072Labels permutation169 permutation2
    _ = mixedMoment B node4341 node4341Labels := by rfl

def raw27073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27073step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw27073step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27073 raw27073Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw27073 raw27073Labels = mixedMoment B raw27073step0 raw27073step0Labels := by
      have hz : ∀ j, raw27073 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27073step0 = (fun i j => raw27073 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27073step0 raw27073; decide +kernel
      have hl : raw27073step0Labels = raw27073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27073 raw27073Labels permutation265 hz
    mixedMoment B raw27073step0 raw27073step0Labels = mixedMoment B raw27073step1 raw27073step1Labels := by
      have ha : raw27073step1 = (fun i j => raw27073step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27073step1 raw27073step0; decide +kernel
      have hl : raw27073step1Labels = raw27073step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27073step0 raw27073step0Labels permutation41 permutation2
    _ = mixedMoment B node4457 node4457Labels := by rfl

def raw27074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw27074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27074step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27074step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27074step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27074step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27074step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27074 raw27074Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw27074 raw27074Labels = mixedMoment B raw27074step0 raw27074step0Labels := by
      have hz : ∀ j, raw27074 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27074step0 = (fun i j => raw27074 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27074step0 raw27074; decide +kernel
      have hl : raw27074step0Labels = raw27074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27074 raw27074Labels permutation520 hz
    mixedMoment B raw27074step0 raw27074step0Labels = mixedMoment B raw27074step1 raw27074step1Labels := by
      have hz : ∀ j, raw27074step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27074step1 = (fun i j => raw27074step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27074step1 raw27074step0; decide +kernel
      have hl : raw27074step1Labels = raw27074step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27074step0 raw27074step0Labels permutation56 hz
    mixedMoment B raw27074step1 raw27074step1Labels = mixedMoment B raw27074step2 raw27074step2Labels := by
      have ha : raw27074step2 = (fun i j => raw27074step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27074step2 raw27074step1; decide +kernel
      have hl : raw27074step2Labels = raw27074step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27074step1 raw27074step1Labels permutation13 permutation2
    _ = mixedMoment B node4498 node4498Labels := by rfl

def raw27075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw27075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27075step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27075step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27075step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27075step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw27075step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27075 raw27075Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw27075 raw27075Labels = mixedMoment B raw27075step0 raw27075step0Labels := by
      have hz : ∀ j, raw27075 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27075step0 = (fun i j => raw27075 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27075step0 raw27075; decide +kernel
      have hl : raw27075step0Labels = raw27075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27075 raw27075Labels permutation590 hz
    mixedMoment B raw27075step0 raw27075step0Labels = mixedMoment B raw27075step1 raw27075step1Labels := by
      have hz : ∀ j, raw27075step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27075step1 = (fun i j => raw27075step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27075step1 raw27075step0; decide +kernel
      have hl : raw27075step1Labels = raw27075step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27075step0 raw27075step0Labels permutation56 hz
    mixedMoment B raw27075step1 raw27075step1Labels = mixedMoment B raw27075step2 raw27075step2Labels := by
      have ha : raw27075step2 = (fun i j => raw27075step1 (permutation13 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27075step2 raw27075step1; decide +kernel
      have hl : raw27075step2Labels = raw27075step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27075step1 raw27075step1Labels permutation13 permutation2
    _ = mixedMoment B node4498 node4498Labels := by rfl

def raw27076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27076step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw27076step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27076 raw27076Labels = mixedMoment B node4173 node4173Labels := by
  calc
    mixedMoment B raw27076 raw27076Labels = mixedMoment B raw27076step0 raw27076step0Labels := by
      have hz : ∀ j, raw27076 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27076step0 = (fun i j => raw27076 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27076step0 raw27076; decide +kernel
      have hl : raw27076step0Labels = raw27076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27076 raw27076Labels permutation265 hz
    mixedMoment B raw27076step0 raw27076step0Labels = mixedMoment B raw27076step1 raw27076step1Labels := by
      have ha : raw27076step1 = (fun i j => raw27076step0 (permutation48 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27076step1 raw27076step0; decide +kernel
      have hl : raw27076step1Labels = raw27076step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27076step0 raw27076step0Labels permutation48 permutation2
    _ = mixedMoment B node4173 node4173Labels := by rfl

def raw27077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw27077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27077 raw27077Labels = mixedMoment B node4342 node4342Labels := by
  calc
    mixedMoment B raw27077 raw27077Labels = mixedMoment B raw27077step0 raw27077step0Labels := by
      have ha : raw27077step0 = (fun i j => raw27077 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27077step0 raw27077; decide +kernel
      have hl : raw27077step0Labels = raw27077Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27077 raw27077Labels permutation168 permutation2
    _ = mixedMoment B node4342 node4342Labels := by rfl

def raw27078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27078step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw27078step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27078 raw27078Labels = mixedMoment B node4474 node4474Labels := by
  calc
    mixedMoment B raw27078 raw27078Labels = mixedMoment B raw27078step0 raw27078step0Labels := by
      have hz : ∀ j, raw27078 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27078step0 = (fun i j => raw27078 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27078step0 raw27078; decide +kernel
      have hl : raw27078step0Labels = raw27078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27078 raw27078Labels permutation265 hz
    mixedMoment B raw27078step0 raw27078step0Labels = mixedMoment B raw27078step1 raw27078step1Labels := by
      have ha : raw27078step1 = (fun i j => raw27078step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27078step1 raw27078step0; decide +kernel
      have hl : raw27078step1Labels = raw27078step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27078step0 raw27078step0Labels permutation35 permutation2
    _ = mixedMoment B node4474 node4474Labels := by rfl

def raw27079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw27079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw27079step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw27079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27079step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw27079step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27079 raw27079Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw27079 raw27079Labels = mixedMoment B raw27079step0 raw27079step0Labels := by
      have hz : ∀ j, raw27079 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27079step0 = (fun i j => raw27079 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27079step0 raw27079; decide +kernel
      have hl : raw27079step0Labels = raw27079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27079 raw27079Labels permutation520 hz
    mixedMoment B raw27079step0 raw27079step0Labels = mixedMoment B raw27079step1 raw27079step1Labels := by
      have hz : ∀ j, raw27079step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27079step1 = (fun i j => raw27079step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27079step1 raw27079step0; decide +kernel
      have hl : raw27079step1Labels = raw27079step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27079step0 raw27079step0Labels permutation56 hz
    mixedMoment B raw27079step1 raw27079step1Labels = mixedMoment B raw27079step2 raw27079step2Labels := by
      have ha : raw27079step2 = (fun i j => raw27079step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27079step2 raw27079step1; decide +kernel
      have hl : raw27079step2Labels = raw27079step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27079step1 raw27079step1Labels permutation12 permutation2
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw27080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw27080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw27080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27080step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw27080step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27080step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw27080step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27080 raw27080Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw27080 raw27080Labels = mixedMoment B raw27080step0 raw27080step0Labels := by
      have hz : ∀ j, raw27080 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27080step0 = (fun i j => raw27080 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27080step0 raw27080; decide +kernel
      have hl : raw27080step0Labels = raw27080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27080 raw27080Labels permutation590 hz
    mixedMoment B raw27080step0 raw27080step0Labels = mixedMoment B raw27080step1 raw27080step1Labels := by
      have hz : ∀ j, raw27080step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27080step1 = (fun i j => raw27080step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27080step1 raw27080step0; decide +kernel
      have hl : raw27080step1Labels = raw27080step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27080step0 raw27080step0Labels permutation56 hz
    mixedMoment B raw27080step1 raw27080step1Labels = mixedMoment B raw27080step2 raw27080step2Labels := by
      have ha : raw27080step2 = (fun i j => raw27080step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27080step2 raw27080step1; decide +kernel
      have hl : raw27080step2Labels = raw27080step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27080step1 raw27080step1Labels permutation12 permutation2
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw27081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27081step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27081 raw27081Labels = mixedMoment B node4176 node4176Labels := by
  calc
    mixedMoment B raw27081 raw27081Labels = mixedMoment B raw27081step0 raw27081step0Labels := by
      have hz : ∀ j, raw27081 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27081step0 = (fun i j => raw27081 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27081step0 raw27081; decide +kernel
      have hl : raw27081step0Labels = raw27081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27081 raw27081Labels permutation265 hz
    mixedMoment B raw27081step0 raw27081step0Labels = mixedMoment B raw27081step1 raw27081step1Labels := by
      have ha : raw27081step1 = (fun i j => raw27081step0 (permutation52 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27081step1 raw27081step0; decide +kernel
      have hl : raw27081step1Labels = raw27081step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27081step0 raw27081step0Labels permutation52 permutation2
    _ = mixedMoment B node4176 node4176Labels := by rfl

def raw27082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27082 raw27082Labels = mixedMoment B node4345 node4345Labels := by
  calc
    mixedMoment B raw27082 raw27082Labels = mixedMoment B raw27082step0 raw27082step0Labels := by
      have ha : raw27082step0 = (fun i j => raw27082 (permutation172 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27082step0 raw27082; decide +kernel
      have hl : raw27082step0Labels = raw27082Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27082 raw27082Labels permutation172 permutation2
    _ = mixedMoment B node4345 node4345Labels := by rfl

def raw27083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27083step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw27083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27083 raw27083Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw27083 raw27083Labels = mixedMoment B raw27083step0 raw27083step0Labels := by
      have hz : ∀ j, raw27083 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27083step0 = (fun i j => raw27083 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27083step0 raw27083; decide +kernel
      have hl : raw27083step0Labels = raw27083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27083 raw27083Labels permutation265 hz
    mixedMoment B raw27083step0 raw27083step0Labels = mixedMoment B raw27083step1 raw27083step1Labels := by
      have ha : raw27083step1 = (fun i j => raw27083step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27083step1 raw27083step0; decide +kernel
      have hl : raw27083step1Labels = raw27083step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27083step0 raw27083step0Labels permutation36 permutation2
    _ = mixedMoment B node4475 node4475Labels := by rfl

def raw27084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27084step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw27084step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27084 raw27084Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw27084 raw27084Labels = mixedMoment B raw27084step0 raw27084step0Labels := by
      have hz : ∀ j, raw27084 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27084step0 = (fun i j => raw27084 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27084step0 raw27084; decide +kernel
      have hl : raw27084step0Labels = raw27084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27084 raw27084Labels permutation265 hz
    mixedMoment B raw27084step0 raw27084step0Labels = mixedMoment B raw27084step1 raw27084step1Labels := by
      have ha : raw27084step1 = (fun i j => raw27084step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27084step1 raw27084step0; decide +kernel
      have hl : raw27084step1Labels = raw27084step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27084step0 raw27084step0Labels permutation42 permutation2
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw27085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw27085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27085step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27085step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27085step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27085 raw27085Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw27085 raw27085Labels = mixedMoment B raw27085step0 raw27085step0Labels := by
      have hz : ∀ j, raw27085 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27085step0 = (fun i j => raw27085 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27085step0 raw27085; decide +kernel
      have hl : raw27085step0Labels = raw27085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27085 raw27085Labels permutation590 hz
    mixedMoment B raw27085step0 raw27085step0Labels = mixedMoment B raw27085step1 raw27085step1Labels := by
      have hz : ∀ j, raw27085step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27085step1 = (fun i j => raw27085step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27085step1 raw27085step0; decide +kernel
      have hl : raw27085step1Labels = raw27085step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27085step0 raw27085step0Labels permutation56 hz
    mixedMoment B raw27085step1 raw27085step1Labels = mixedMoment B raw27085step2 raw27085step2Labels := by
      have ha : raw27085step2 = (fun i j => raw27085step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27085step2 raw27085step1; decide +kernel
      have hl : raw27085step2Labels = raw27085step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27085step1 raw27085step1Labels permutation10 permutation2
    _ = mixedMoment B node4503 node4503Labels := by rfl

def raw27086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27086 raw27086Labels = mixedMoment B node4176 node4176Labels := by
  calc
    mixedMoment B raw27086 raw27086Labels = mixedMoment B raw27086step0 raw27086step0Labels := by
      have hz : ∀ j, raw27086 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27086step0 = (fun i j => raw27086 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27086step0 raw27086; decide +kernel
      have hl : raw27086step0Labels = raw27086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27086 raw27086Labels permutation265 hz
    mixedMoment B raw27086step0 raw27086step0Labels = mixedMoment B raw27086step1 raw27086step1Labels := by
      have ha : raw27086step1 = (fun i j => raw27086step0 (permutation46 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27086step1 raw27086step0; decide +kernel
      have hl : raw27086step1Labels = raw27086step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27086step0 raw27086step0Labels permutation46 permutation2
    _ = mixedMoment B node4176 node4176Labels := by rfl

def raw27087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27087 raw27087Labels = mixedMoment B node4345 node4345Labels := by
  calc
    mixedMoment B raw27087 raw27087Labels = mixedMoment B raw27087step0 raw27087step0Labels := by
      have ha : raw27087step0 = (fun i j => raw27087 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27087step0 raw27087; decide +kernel
      have hl : raw27087step0Labels = raw27087Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27087 raw27087Labels permutation166 permutation2
    _ = mixedMoment B node4345 node4345Labels := by rfl

def raw27088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw27088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27088 raw27088Labels = mixedMoment B node4475 node4475Labels := by
  calc
    mixedMoment B raw27088 raw27088Labels = mixedMoment B raw27088step0 raw27088step0Labels := by
      have hz : ∀ j, raw27088 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27088step0 = (fun i j => raw27088 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27088step0 raw27088; decide +kernel
      have hl : raw27088step0Labels = raw27088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27088 raw27088Labels permutation265 hz
    mixedMoment B raw27088step0 raw27088step0Labels = mixedMoment B raw27088step1 raw27088step1Labels := by
      have ha : raw27088step1 = (fun i j => raw27088step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27088step1 raw27088step0; decide +kernel
      have hl : raw27088step1Labels = raw27088step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27088step0 raw27088step0Labels permutation34 permutation2
    _ = mixedMoment B node4475 node4475Labels := by rfl

def raw27089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw27089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27089 raw27089Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw27089 raw27089Labels = mixedMoment B raw27089step0 raw27089step0Labels := by
      have hz : ∀ j, raw27089 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27089step0 = (fun i j => raw27089 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27089step0 raw27089; decide +kernel
      have hl : raw27089step0Labels = raw27089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27089 raw27089Labels permutation265 hz
    mixedMoment B raw27089step0 raw27089step0Labels = mixedMoment B raw27089step1 raw27089step1Labels := by
      have ha : raw27089step1 = (fun i j => raw27089step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27089step1 raw27089step0; decide +kernel
      have hl : raw27089step1Labels = raw27089step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27089step0 raw27089step0Labels permutation40 permutation2
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw27090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw27090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27090step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27090step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27090step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27090 raw27090Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw27090 raw27090Labels = mixedMoment B raw27090step0 raw27090step0Labels := by
      have hz : ∀ j, raw27090 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27090step0 = (fun i j => raw27090 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27090step0 raw27090; decide +kernel
      have hl : raw27090step0Labels = raw27090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27090 raw27090Labels permutation520 hz
    mixedMoment B raw27090step0 raw27090step0Labels = mixedMoment B raw27090step1 raw27090step1Labels := by
      have hz : ∀ j, raw27090step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27090step1 = (fun i j => raw27090step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27090step1 raw27090step0; decide +kernel
      have hl : raw27090step1Labels = raw27090step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27090step0 raw27090step0Labels permutation56 hz
    mixedMoment B raw27090step1 raw27090step1Labels = mixedMoment B raw27090step2 raw27090step2Labels := by
      have ha : raw27090step2 = (fun i j => raw27090step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw27090step2 raw27090step1; decide +kernel
      have hl : raw27090step2Labels = raw27090step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27090step1 raw27090step1Labels permutation10 permutation2
    _ = mixedMoment B node4503 node4503Labels := by rfl

def raw27091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27091Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27091step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27091step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27091step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27091step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27091 raw27091Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw27091 raw27091Labels = mixedMoment B raw27091step0 raw27091step0Labels := by
      have ha : raw27091step0 = (fun i j => raw27091 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27091step0 raw27091; decide +kernel
      have hl : raw27091step0Labels = raw27091Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27091 raw27091Labels permutation169 permutation7
    mixedMoment B raw27091step0 raw27091step0Labels = mixedMoment B raw27091step1 raw27091step1Labels := by
      have ha : raw27091step1 = -raw27091step0 := by apply Matrix.ext; change ∀ i j, raw27091step1 i j = -(raw27091step0 i j); unfold raw27091step1 raw27091step0; decide +kernel
      have hl : raw27091step1Labels = raw27091step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27091step1 raw27091step1Labels = mixedMoment B raw27091step2 raw27091step2Labels := by
      have ha : raw27091step2 = raw27091step1 := by apply Matrix.ext; unfold raw27091step2 raw27091step1; decide +kernel
      have hl : raw27091step1Labels = labelEmbedding1 ∘ raw27091step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27091step1 raw27091step1Labels raw27091step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2191 node2191Labels := by rfl

def raw27092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27092Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27092step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27092step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27092step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27092step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27092step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27092step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27092 raw27092Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw27092 raw27092Labels = mixedMoment B raw27092step0 raw27092step0Labels := by
      have hz : ∀ j, raw27092 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27092step0 = (fun i j => raw27092 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27092step0 raw27092; decide +kernel
      have hl : raw27092step0Labels = raw27092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27092 raw27092Labels permutation265 hz
    mixedMoment B raw27092step0 raw27092step0Labels = mixedMoment B raw27092step1 raw27092step1Labels := by
      have ha : raw27092step1 = (fun i j => raw27092step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27092step1 raw27092step0; decide +kernel
      have hl : raw27092step1Labels = raw27092step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27092step0 raw27092step0Labels permutation49 permutation7
    mixedMoment B raw27092step1 raw27092step1Labels = mixedMoment B raw27092step2 raw27092step2Labels := by
      have ha : raw27092step2 = -raw27092step1 := by apply Matrix.ext; change ∀ i j, raw27092step2 i j = -(raw27092step1 i j); unfold raw27092step2 raw27092step1; decide +kernel
      have hl : raw27092step2Labels = raw27092step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27092step2 raw27092step2Labels = mixedMoment B raw27092step3 raw27092step3Labels := by
      have ha : raw27092step3 = raw27092step2 := by apply Matrix.ext; unfold raw27092step3 raw27092step2; decide +kernel
      have hl : raw27092step2Labels = labelEmbedding1 ∘ raw27092step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27092step2 raw27092step2Labels raw27092step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2245 node2245Labels := by rfl

def raw27093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27093Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27093step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw27093step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27093step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw27093step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27093step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw27093step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27093 raw27093Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw27093 raw27093Labels = mixedMoment B raw27093step0 raw27093step0Labels := by
      have hz : ∀ j, raw27093 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27093step0 = (fun i j => raw27093 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27093step0 raw27093; decide +kernel
      have hl : raw27093step0Labels = raw27093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27093 raw27093Labels permutation265 hz
    mixedMoment B raw27093step0 raw27093step0Labels = mixedMoment B raw27093step1 raw27093step1Labels := by
      have ha : raw27093step1 = (fun i j => raw27093step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27093step1 raw27093step0; decide +kernel
      have hl : raw27093step1Labels = raw27093step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27093step0 raw27093step0Labels permutation49 permutation7
    mixedMoment B raw27093step1 raw27093step1Labels = mixedMoment B raw27093step2 raw27093step2Labels := by
      have ha : raw27093step2 = -raw27093step1 := by apply Matrix.ext; change ∀ i j, raw27093step2 i j = -(raw27093step1 i j); unfold raw27093step2 raw27093step1; decide +kernel
      have hl : raw27093step2Labels = raw27093step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27093step2 raw27093step2Labels = mixedMoment B raw27093step3 raw27093step3Labels := by
      have ha : raw27093step3 = raw27093step2 := by apply Matrix.ext; unfold raw27093step3 raw27093step2; decide +kernel
      have hl : raw27093step2Labels = labelEmbedding1 ∘ raw27093step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27093step2 raw27093step2Labels raw27093step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2244 node2244Labels := by rfl

def raw27094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw27094Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27094step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27094step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27094step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27094step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27094step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27094step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27094step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27094step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27094step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27094 raw27094Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw27094 raw27094Labels = mixedMoment B raw27094step0 raw27094step0Labels := by
      have hz : ∀ j, raw27094 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27094step0 = (fun i j => raw27094 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27094step0 raw27094; decide +kernel
      have hl : raw27094step0Labels = raw27094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27094 raw27094Labels permutation520 hz
    mixedMoment B raw27094step0 raw27094step0Labels = mixedMoment B raw27094step1 raw27094step1Labels := by
      have hz : ∀ j, raw27094step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27094step1 = (fun i j => raw27094step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27094step1 raw27094step0; decide +kernel
      have hl : raw27094step1Labels = raw27094step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27094step0 raw27094step0Labels permutation56 hz
    mixedMoment B raw27094step1 raw27094step1Labels = mixedMoment B raw27094step2 raw27094step2Labels := by
      have ha : raw27094step2 = (fun i j => raw27094step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27094step2 raw27094step1; decide +kernel
      have hl : raw27094step2Labels = raw27094step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27094step1 raw27094step1Labels permutation13 permutation7
    mixedMoment B raw27094step2 raw27094step2Labels = mixedMoment B raw27094step3 raw27094step3Labels := by
      have ha : raw27094step3 = -raw27094step2 := by apply Matrix.ext; change ∀ i j, raw27094step3 i j = -(raw27094step2 i j); unfold raw27094step3 raw27094step2; decide +kernel
      have hl : raw27094step3Labels = raw27094step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27094step3 raw27094step3Labels = mixedMoment B raw27094step4 raw27094step4Labels := by
      have ha : raw27094step4 = raw27094step3 := by apply Matrix.ext; unfold raw27094step4 raw27094step3; decide +kernel
      have hl : raw27094step3Labels = labelEmbedding1 ∘ raw27094step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27094step3 raw27094step3Labels raw27094step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2265 node2265Labels := by rfl

def raw27095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw27095Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27095step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27095step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27095step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27095step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27095step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27095step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27095step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27095step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27095 raw27095Labels = mixedMoment B node2265 node2265Labels := by
  calc
    mixedMoment B raw27095 raw27095Labels = mixedMoment B raw27095step0 raw27095step0Labels := by
      have hz : ∀ j, raw27095 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27095step0 = (fun i j => raw27095 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27095step0 raw27095; decide +kernel
      have hl : raw27095step0Labels = raw27095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27095 raw27095Labels permutation590 hz
    mixedMoment B raw27095step0 raw27095step0Labels = mixedMoment B raw27095step1 raw27095step1Labels := by
      have hz : ∀ j, raw27095step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27095step1 = (fun i j => raw27095step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27095step1 raw27095step0; decide +kernel
      have hl : raw27095step1Labels = raw27095step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27095step0 raw27095step0Labels permutation56 hz
    mixedMoment B raw27095step1 raw27095step1Labels = mixedMoment B raw27095step2 raw27095step2Labels := by
      have ha : raw27095step2 = (fun i j => raw27095step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27095step2 raw27095step1; decide +kernel
      have hl : raw27095step2Labels = raw27095step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27095step1 raw27095step1Labels permutation13 permutation7
    mixedMoment B raw27095step2 raw27095step2Labels = mixedMoment B raw27095step3 raw27095step3Labels := by
      have ha : raw27095step3 = -raw27095step2 := by apply Matrix.ext; change ∀ i j, raw27095step3 i j = -(raw27095step2 i j); unfold raw27095step3 raw27095step2; decide +kernel
      have hl : raw27095step3Labels = raw27095step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27095step3 raw27095step3Labels = mixedMoment B raw27095step4 raw27095step4Labels := by
      have ha : raw27095step4 = raw27095step3 := by apply Matrix.ext; unfold raw27095step4 raw27095step3; decide +kernel
      have hl : raw27095step3Labels = labelEmbedding1 ∘ raw27095step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27095step3 raw27095step3Labels raw27095step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2265 node2265Labels := by rfl

def raw27096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27096Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27096step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27096step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27096step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27096step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27096step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27096 raw27096Labels = mixedMoment B node1502 node1502Labels := by
  calc
    mixedMoment B raw27096 raw27096Labels = mixedMoment B raw27096step0 raw27096step0Labels := by
      have ha : raw27096step0 = (fun i j => raw27096 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27096step0 raw27096; decide +kernel
      have hl : raw27096step0Labels = raw27096Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27096 raw27096Labels permutation169 permutation7
    mixedMoment B raw27096step0 raw27096step0Labels = mixedMoment B raw27096step1 raw27096step1Labels := by
      have ha : raw27096step1 = -raw27096step0 := by apply Matrix.ext; change ∀ i j, raw27096step1 i j = -(raw27096step0 i j); unfold raw27096step1 raw27096step0; decide +kernel
      have hl : raw27096step1Labels = raw27096step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27096step1 raw27096step1Labels = mixedMoment B raw27096step2 raw27096step2Labels := by
      have ha : raw27096step2 = raw27096step1 := by apply Matrix.ext; unfold raw27096step2 raw27096step1; decide +kernel
      have hl : raw27096step1Labels = labelEmbedding1 ∘ raw27096step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27096step1 raw27096step1Labels raw27096step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1502 node1502Labels := by rfl

def raw27097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27097Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw27097step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27097step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27097step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw27097step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27097 raw27097Labels = mixedMoment B node1699 node1699Labels := by
  calc
    mixedMoment B raw27097 raw27097Labels = mixedMoment B raw27097step0 raw27097step0Labels := by
      have ha : raw27097step0 = (fun i j => raw27097 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27097step0 raw27097; decide +kernel
      have hl : raw27097step0Labels = raw27097Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27097 raw27097Labels permutation169 permutation7
    mixedMoment B raw27097step0 raw27097step0Labels = mixedMoment B raw27097step1 raw27097step1Labels := by
      have ha : raw27097step1 = -raw27097step0 := by apply Matrix.ext; change ∀ i j, raw27097step1 i j = -(raw27097step0 i j); unfold raw27097step1 raw27097step0; decide +kernel
      have hl : raw27097step1Labels = raw27097step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27097step1 raw27097step1Labels = mixedMoment B raw27097step2 raw27097step2Labels := by
      have ha : raw27097step2 = raw27097step1 := by apply Matrix.ext; unfold raw27097step2 raw27097step1; decide +kernel
      have hl : raw27097step1Labels = labelEmbedding1 ∘ raw27097step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27097step1 raw27097step1Labels raw27097step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1699 node1699Labels := by rfl

def raw27098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27098Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw27098step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27098step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw27098step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27098step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw27098step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27098 raw27098Labels = mixedMoment B node1698 node1698Labels := by
  calc
    mixedMoment B raw27098 raw27098Labels = mixedMoment B raw27098step0 raw27098step0Labels := by
      have ha : raw27098step0 = (fun i j => raw27098 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27098step0 raw27098; decide +kernel
      have hl : raw27098step0Labels = raw27098Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27098 raw27098Labels permutation169 permutation7
    mixedMoment B raw27098step0 raw27098step0Labels = mixedMoment B raw27098step1 raw27098step1Labels := by
      have ha : raw27098step1 = -raw27098step0 := by apply Matrix.ext; change ∀ i j, raw27098step1 i j = -(raw27098step0 i j); unfold raw27098step1 raw27098step0; decide +kernel
      have hl : raw27098step1Labels = raw27098step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27098step1 raw27098step1Labels = mixedMoment B raw27098step2 raw27098step2Labels := by
      have ha : raw27098step2 = raw27098step1 := by apply Matrix.ext; unfold raw27098step2 raw27098step1; decide +kernel
      have hl : raw27098step1Labels = labelEmbedding1 ∘ raw27098step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27098step1 raw27098step1Labels raw27098step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1698 node1698Labels := by rfl

def raw27099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw27099Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27099step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27099step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27099step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27099step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27099step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27099step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27099 raw27099Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw27099 raw27099Labels = mixedMoment B raw27099step0 raw27099step0Labels := by
      have hz : ∀ j, raw27099 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27099step0 = (fun i j => raw27099 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27099step0 raw27099; decide +kernel
      have hl : raw27099step0Labels = raw27099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27099 raw27099Labels permutation520 hz
    mixedMoment B raw27099step0 raw27099step0Labels = mixedMoment B raw27099step1 raw27099step1Labels := by
      have ha : raw27099step1 = (fun i j => raw27099step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27099step1 raw27099step0; decide +kernel
      have hl : raw27099step1Labels = raw27099step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27099step0 raw27099step0Labels permutation37 permutation7
    mixedMoment B raw27099step1 raw27099step1Labels = mixedMoment B raw27099step2 raw27099step2Labels := by
      have ha : raw27099step2 = -raw27099step1 := by apply Matrix.ext; change ∀ i j, raw27099step2 i j = -(raw27099step1 i j); unfold raw27099step2 raw27099step1; decide +kernel
      have hl : raw27099step2Labels = raw27099step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27099step2 raw27099step2Labels = mixedMoment B raw27099step3 raw27099step3Labels := by
      have ha : raw27099step3 = raw27099step2 := by apply Matrix.ext; unfold raw27099step3 raw27099step2; decide +kernel
      have hl : raw27099step2Labels = labelEmbedding1 ∘ raw27099step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27099step2 raw27099step2Labels raw27099step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

def raw27100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw27100Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27100step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw27100step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27100step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27100step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27100step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw27100step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27100 raw27100Labels = mixedMoment B node1708 node1708Labels := by
  calc
    mixedMoment B raw27100 raw27100Labels = mixedMoment B raw27100step0 raw27100step0Labels := by
      have hz : ∀ j, raw27100 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27100step0 = (fun i j => raw27100 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27100step0 raw27100; decide +kernel
      have hl : raw27100step0Labels = raw27100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27100 raw27100Labels permutation590 hz
    mixedMoment B raw27100step0 raw27100step0Labels = mixedMoment B raw27100step1 raw27100step1Labels := by
      have ha : raw27100step1 = (fun i j => raw27100step0 (permutation37 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27100step1 raw27100step0; decide +kernel
      have hl : raw27100step1Labels = raw27100step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27100step0 raw27100step0Labels permutation37 permutation7
    mixedMoment B raw27100step1 raw27100step1Labels = mixedMoment B raw27100step2 raw27100step2Labels := by
      have ha : raw27100step2 = -raw27100step1 := by apply Matrix.ext; change ∀ i j, raw27100step2 i j = -(raw27100step1 i j); unfold raw27100step2 raw27100step1; decide +kernel
      have hl : raw27100step2Labels = raw27100step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27100step2 raw27100step2Labels = mixedMoment B raw27100step3 raw27100step3Labels := by
      have ha : raw27100step3 = raw27100step2 := by apply Matrix.ext; unfold raw27100step3 raw27100step2; decide +kernel
      have hl : raw27100step2Labels = labelEmbedding1 ∘ raw27100step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27100step2 raw27100step2Labels raw27100step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1708 node1708Labels := by rfl

def raw27101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27101Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27101step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw27101step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27101step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw27101step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27101step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw27101step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27101 raw27101Labels = mixedMoment B node1507 node1507Labels := by
  calc
    mixedMoment B raw27101 raw27101Labels = mixedMoment B raw27101step0 raw27101step0Labels := by
      have hz : ∀ j, raw27101 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27101step0 = (fun i j => raw27101 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27101step0 raw27101; decide +kernel
      have hl : raw27101step0Labels = raw27101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27101 raw27101Labels permutation265 hz
    mixedMoment B raw27101step0 raw27101step0Labels = mixedMoment B raw27101step1 raw27101step1Labels := by
      have ha : raw27101step1 = (fun i j => raw27101step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27101step1 raw27101step0; decide +kernel
      have hl : raw27101step1Labels = raw27101step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27101step0 raw27101step0Labels permutation49 permutation7
    mixedMoment B raw27101step1 raw27101step1Labels = mixedMoment B raw27101step2 raw27101step2Labels := by
      have ha : raw27101step2 = -raw27101step1 := by apply Matrix.ext; change ∀ i j, raw27101step2 i j = -(raw27101step1 i j); unfold raw27101step2 raw27101step1; decide +kernel
      have hl : raw27101step2Labels = raw27101step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27101step2 raw27101step2Labels = mixedMoment B raw27101step3 raw27101step3Labels := by
      have ha : raw27101step3 = raw27101step2 := by apply Matrix.ext; unfold raw27101step3 raw27101step2; decide +kernel
      have hl : raw27101step2Labels = labelEmbedding1 ∘ raw27101step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27101step2 raw27101step2Labels raw27101step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1507 node1507Labels := by rfl

def raw27102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27102Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw27102step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27102step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw27102step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27102step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw27102step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27102 raw27102Labels = mixedMoment B node1664 node1664Labels := by
  calc
    mixedMoment B raw27102 raw27102Labels = mixedMoment B raw27102step0 raw27102step0Labels := by
      have ha : raw27102step0 = (fun i j => raw27102 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27102step0 raw27102; decide +kernel
      have hl : raw27102step0Labels = raw27102Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27102 raw27102Labels permutation169 permutation7
    mixedMoment B raw27102step0 raw27102step0Labels = mixedMoment B raw27102step1 raw27102step1Labels := by
      have ha : raw27102step1 = -raw27102step0 := by apply Matrix.ext; change ∀ i j, raw27102step1 i j = -(raw27102step0 i j); unfold raw27102step1 raw27102step0; decide +kernel
      have hl : raw27102step1Labels = raw27102step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27102step1 raw27102step1Labels = mixedMoment B raw27102step2 raw27102step2Labels := by
      have ha : raw27102step2 = raw27102step1 := by apply Matrix.ext; unfold raw27102step2 raw27102step1; decide +kernel
      have hl : raw27102step1Labels = labelEmbedding1 ∘ raw27102step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27102step1 raw27102step1Labels raw27102step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1664 node1664Labels := by rfl

def raw27103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27103Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27103step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw27103step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw27103step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27103step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw27103step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27103 raw27103Labels = mixedMoment B node1707 node1707Labels := by
  calc
    mixedMoment B raw27103 raw27103Labels = mixedMoment B raw27103step0 raw27103step0Labels := by
      have hz : ∀ j, raw27103 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27103step0 = (fun i j => raw27103 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27103step0 raw27103; decide +kernel
      have hl : raw27103step0Labels = raw27103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27103 raw27103Labels permutation265 hz
    mixedMoment B raw27103step0 raw27103step0Labels = mixedMoment B raw27103step1 raw27103step1Labels := by
      have ha : raw27103step1 = (fun i j => raw27103step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27103step1 raw27103step0; decide +kernel
      have hl : raw27103step1Labels = raw27103step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27103step0 raw27103step0Labels permutation49 permutation7
    mixedMoment B raw27103step1 raw27103step1Labels = mixedMoment B raw27103step2 raw27103step2Labels := by
      have ha : raw27103step2 = -raw27103step1 := by apply Matrix.ext; change ∀ i j, raw27103step2 i j = -(raw27103step1 i j); unfold raw27103step2 raw27103step1; decide +kernel
      have hl : raw27103step2Labels = raw27103step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27103step2 raw27103step2Labels = mixedMoment B raw27103step3 raw27103step3Labels := by
      have ha : raw27103step3 = raw27103step2 := by apply Matrix.ext; unfold raw27103step3 raw27103step2; decide +kernel
      have hl : raw27103step2Labels = labelEmbedding1 ∘ raw27103step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27103step2 raw27103step2Labels raw27103step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1707 node1707Labels := by rfl

def raw27104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw27104Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27104step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27104step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27104step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw27104step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27104step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw27104step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27104step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw27104step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27104 raw27104Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw27104 raw27104Labels = mixedMoment B raw27104step0 raw27104step0Labels := by
      have hz : ∀ j, raw27104 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27104step0 = (fun i j => raw27104 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27104step0 raw27104; decide +kernel
      have hl : raw27104step0Labels = raw27104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27104 raw27104Labels permutation520 hz
    mixedMoment B raw27104step0 raw27104step0Labels = mixedMoment B raw27104step1 raw27104step1Labels := by
      have hz : ∀ j, raw27104step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27104step1 = (fun i j => raw27104step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27104step1 raw27104step0; decide +kernel
      have hl : raw27104step1Labels = raw27104step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27104step0 raw27104step0Labels permutation56 hz
    mixedMoment B raw27104step1 raw27104step1Labels = mixedMoment B raw27104step2 raw27104step2Labels := by
      have ha : raw27104step2 = (fun i j => raw27104step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27104step2 raw27104step1; decide +kernel
      have hl : raw27104step2Labels = raw27104step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27104step1 raw27104step1Labels permutation13 permutation7
    mixedMoment B raw27104step2 raw27104step2Labels = mixedMoment B raw27104step3 raw27104step3Labels := by
      have ha : raw27104step3 = -raw27104step2 := by apply Matrix.ext; change ∀ i j, raw27104step3 i j = -(raw27104step2 i j); unfold raw27104step3 raw27104step2; decide +kernel
      have hl : raw27104step3Labels = raw27104step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27104step3 raw27104step3Labels = mixedMoment B raw27104step4 raw27104step4Labels := by
      have ha : raw27104step4 = raw27104step3 := by apply Matrix.ext; unfold raw27104step4 raw27104step3; decide +kernel
      have hl : raw27104step3Labels = labelEmbedding1 ∘ raw27104step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27104step3 raw27104step3Labels raw27104step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

def raw27105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw27105Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27105step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![2, 0, -2], ![1, 0, -1], ![1, -1, 0]]
def raw27105step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw27105step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27105step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw27105step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27105step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw27105step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27105 raw27105Labels = mixedMoment B node1727 node1727Labels := by
  calc
    mixedMoment B raw27105 raw27105Labels = mixedMoment B raw27105step0 raw27105step0Labels := by
      have hz : ∀ j, raw27105 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27105step0 = (fun i j => raw27105 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27105step0 raw27105; decide +kernel
      have hl : raw27105step0Labels = raw27105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27105 raw27105Labels permutation590 hz
    mixedMoment B raw27105step0 raw27105step0Labels = mixedMoment B raw27105step1 raw27105step1Labels := by
      have hz : ∀ j, raw27105step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27105step1 = (fun i j => raw27105step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27105step1 raw27105step0; decide +kernel
      have hl : raw27105step1Labels = raw27105step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27105step0 raw27105step0Labels permutation56 hz
    mixedMoment B raw27105step1 raw27105step1Labels = mixedMoment B raw27105step2 raw27105step2Labels := by
      have ha : raw27105step2 = (fun i j => raw27105step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27105step2 raw27105step1; decide +kernel
      have hl : raw27105step2Labels = raw27105step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27105step1 raw27105step1Labels permutation13 permutation7
    mixedMoment B raw27105step2 raw27105step2Labels = mixedMoment B raw27105step3 raw27105step3Labels := by
      have ha : raw27105step3 = -raw27105step2 := by apply Matrix.ext; change ∀ i j, raw27105step3 i j = -(raw27105step2 i j); unfold raw27105step3 raw27105step2; decide +kernel
      have hl : raw27105step3Labels = raw27105step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27105step3 raw27105step3Labels = mixedMoment B raw27105step4 raw27105step4Labels := by
      have ha : raw27105step4 = raw27105step3 := by apply Matrix.ext; unfold raw27105step4 raw27105step3; decide +kernel
      have hl : raw27105step3Labels = labelEmbedding1 ∘ raw27105step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27105step3 raw27105step3Labels raw27105step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1727 node1727Labels := by rfl

def raw27106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27106Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27106step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw27106step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27106step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27106step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27106step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27106step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27106 raw27106Labels = mixedMoment B node1508 node1508Labels := by
  calc
    mixedMoment B raw27106 raw27106Labels = mixedMoment B raw27106step0 raw27106step0Labels := by
      have hz : ∀ j, raw27106 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27106step0 = (fun i j => raw27106 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27106step0 raw27106; decide +kernel
      have hl : raw27106step0Labels = raw27106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27106 raw27106Labels permutation265 hz
    mixedMoment B raw27106step0 raw27106step0Labels = mixedMoment B raw27106step1 raw27106step1Labels := by
      have ha : raw27106step1 = (fun i j => raw27106step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27106step1 raw27106step0; decide +kernel
      have hl : raw27106step1Labels = raw27106step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27106step0 raw27106step0Labels permutation49 permutation7
    mixedMoment B raw27106step1 raw27106step1Labels = mixedMoment B raw27106step2 raw27106step2Labels := by
      have ha : raw27106step2 = -raw27106step1 := by apply Matrix.ext; change ∀ i j, raw27106step2 i j = -(raw27106step1 i j); unfold raw27106step2 raw27106step1; decide +kernel
      have hl : raw27106step2Labels = raw27106step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27106step2 raw27106step2Labels = mixedMoment B raw27106step3 raw27106step3Labels := by
      have ha : raw27106step3 = raw27106step2 := by apply Matrix.ext; unfold raw27106step3 raw27106step2; decide +kernel
      have hl : raw27106step2Labels = labelEmbedding1 ∘ raw27106step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27106step2 raw27106step2Labels raw27106step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1508 node1508Labels := by rfl

def raw27107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27107Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw27107step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27107step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27107step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27107step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27107step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27107 raw27107Labels = mixedMoment B node1665 node1665Labels := by
  calc
    mixedMoment B raw27107 raw27107Labels = mixedMoment B raw27107step0 raw27107step0Labels := by
      have ha : raw27107step0 = (fun i j => raw27107 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27107step0 raw27107; decide +kernel
      have hl : raw27107step0Labels = raw27107Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27107 raw27107Labels permutation169 permutation7
    mixedMoment B raw27107step0 raw27107step0Labels = mixedMoment B raw27107step1 raw27107step1Labels := by
      have ha : raw27107step1 = -raw27107step0 := by apply Matrix.ext; change ∀ i j, raw27107step1 i j = -(raw27107step0 i j); unfold raw27107step1 raw27107step0; decide +kernel
      have hl : raw27107step1Labels = raw27107step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27107step1 raw27107step1Labels = mixedMoment B raw27107step2 raw27107step2Labels := by
      have ha : raw27107step2 = raw27107step1 := by apply Matrix.ext; unfold raw27107step2 raw27107step1; decide +kernel
      have hl : raw27107step1Labels = labelEmbedding1 ∘ raw27107step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27107step1 raw27107step1Labels raw27107step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1665 node1665Labels := by rfl

def raw27108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27108Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw27108step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw27108step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27108step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27108step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw27108step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27108 raw27108Labels = mixedMoment B node1709 node1709Labels := by
  calc
    mixedMoment B raw27108 raw27108Labels = mixedMoment B raw27108step0 raw27108step0Labels := by
      have hz : ∀ j, raw27108 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27108step0 = (fun i j => raw27108 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27108step0 raw27108; decide +kernel
      have hl : raw27108step0Labels = raw27108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27108 raw27108Labels permutation265 hz
    mixedMoment B raw27108step0 raw27108step0Labels = mixedMoment B raw27108step1 raw27108step1Labels := by
      have ha : raw27108step1 = (fun i j => raw27108step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27108step1 raw27108step0; decide +kernel
      have hl : raw27108step1Labels = raw27108step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27108step0 raw27108step0Labels permutation49 permutation7
    mixedMoment B raw27108step1 raw27108step1Labels = mixedMoment B raw27108step2 raw27108step2Labels := by
      have ha : raw27108step2 = -raw27108step1 := by apply Matrix.ext; change ∀ i j, raw27108step2 i j = -(raw27108step1 i j); unfold raw27108step2 raw27108step1; decide +kernel
      have hl : raw27108step2Labels = raw27108step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27108step2 raw27108step2Labels = mixedMoment B raw27108step3 raw27108step3Labels := by
      have ha : raw27108step3 = raw27108step2 := by apply Matrix.ext; unfold raw27108step3 raw27108step2; decide +kernel
      have hl : raw27108step2Labels = labelEmbedding1 ∘ raw27108step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27108step2 raw27108step2Labels raw27108step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1709 node1709Labels := by rfl

def raw27109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw27109Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw27109step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw27109step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27109step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw27109step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27109step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27109step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27109step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27109step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27109 raw27109Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw27109 raw27109Labels = mixedMoment B raw27109step0 raw27109step0Labels := by
      have hz : ∀ j, raw27109 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27109step0 = (fun i j => raw27109 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27109step0 raw27109; decide +kernel
      have hl : raw27109step0Labels = raw27109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27109 raw27109Labels permutation520 hz
    mixedMoment B raw27109step0 raw27109step0Labels = mixedMoment B raw27109step1 raw27109step1Labels := by
      have hz : ∀ j, raw27109step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27109step1 = (fun i j => raw27109step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27109step1 raw27109step0; decide +kernel
      have hl : raw27109step1Labels = raw27109step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27109step0 raw27109step0Labels permutation56 hz
    mixedMoment B raw27109step1 raw27109step1Labels = mixedMoment B raw27109step2 raw27109step2Labels := by
      have ha : raw27109step2 = (fun i j => raw27109step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27109step2 raw27109step1; decide +kernel
      have hl : raw27109step2Labels = raw27109step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27109step1 raw27109step1Labels permutation13 permutation7
    mixedMoment B raw27109step2 raw27109step2Labels = mixedMoment B raw27109step3 raw27109step3Labels := by
      have ha : raw27109step3 = -raw27109step2 := by apply Matrix.ext; change ∀ i j, raw27109step3 i j = -(raw27109step2 i j); unfold raw27109step3 raw27109step2; decide +kernel
      have hl : raw27109step3Labels = raw27109step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27109step3 raw27109step3Labels = mixedMoment B raw27109step4 raw27109step4Labels := by
      have ha : raw27109step4 = raw27109step3 := by apply Matrix.ext; unfold raw27109step4 raw27109step3; decide +kernel
      have hl : raw27109step3Labels = labelEmbedding1 ∘ raw27109step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27109step3 raw27109step3Labels raw27109step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

def raw27110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw27110Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw27110step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![2, -1, -1], ![1, -1, 0]]
def raw27110step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27110step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw27110step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27110step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27110step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27110step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw27110step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27110 raw27110Labels = mixedMoment B node1728 node1728Labels := by
  calc
    mixedMoment B raw27110 raw27110Labels = mixedMoment B raw27110step0 raw27110step0Labels := by
      have hz : ∀ j, raw27110 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27110step0 = (fun i j => raw27110 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27110step0 raw27110; decide +kernel
      have hl : raw27110step0Labels = raw27110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27110 raw27110Labels permutation590 hz
    mixedMoment B raw27110step0 raw27110step0Labels = mixedMoment B raw27110step1 raw27110step1Labels := by
      have hz : ∀ j, raw27110step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27110step1 = (fun i j => raw27110step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27110step1 raw27110step0; decide +kernel
      have hl : raw27110step1Labels = raw27110step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27110step0 raw27110step0Labels permutation56 hz
    mixedMoment B raw27110step1 raw27110step1Labels = mixedMoment B raw27110step2 raw27110step2Labels := by
      have ha : raw27110step2 = (fun i j => raw27110step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27110step2 raw27110step1; decide +kernel
      have hl : raw27110step2Labels = raw27110step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27110step1 raw27110step1Labels permutation13 permutation7
    mixedMoment B raw27110step2 raw27110step2Labels = mixedMoment B raw27110step3 raw27110step3Labels := by
      have ha : raw27110step3 = -raw27110step2 := by apply Matrix.ext; change ∀ i j, raw27110step3 i j = -(raw27110step2 i j); unfold raw27110step3 raw27110step2; decide +kernel
      have hl : raw27110step3Labels = raw27110step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27110step3 raw27110step3Labels = mixedMoment B raw27110step4 raw27110step4Labels := by
      have ha : raw27110step4 = raw27110step3 := by apply Matrix.ext; unfold raw27110step4 raw27110step3; decide +kernel
      have hl : raw27110step3Labels = labelEmbedding1 ∘ raw27110step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27110step3 raw27110step3Labels raw27110step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1728 node1728Labels := by rfl

def raw27111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27111Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27111step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw27111step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27111step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27111step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27111step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27111step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27111 raw27111Labels = mixedMoment B node1512 node1512Labels := by
  calc
    mixedMoment B raw27111 raw27111Labels = mixedMoment B raw27111step0 raw27111step0Labels := by
      have hz : ∀ j, raw27111 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27111step0 = (fun i j => raw27111 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27111step0 raw27111; decide +kernel
      have hl : raw27111step0Labels = raw27111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27111 raw27111Labels permutation265 hz
    mixedMoment B raw27111step0 raw27111step0Labels = mixedMoment B raw27111step1 raw27111step1Labels := by
      have ha : raw27111step1 = (fun i j => raw27111step0 (permutation55 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27111step1 raw27111step0; decide +kernel
      have hl : raw27111step1Labels = raw27111step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27111step0 raw27111step0Labels permutation55 permutation7
    mixedMoment B raw27111step1 raw27111step1Labels = mixedMoment B raw27111step2 raw27111step2Labels := by
      have ha : raw27111step2 = -raw27111step1 := by apply Matrix.ext; change ∀ i j, raw27111step2 i j = -(raw27111step1 i j); unfold raw27111step2 raw27111step1; decide +kernel
      have hl : raw27111step2Labels = raw27111step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27111step2 raw27111step2Labels = mixedMoment B raw27111step3 raw27111step3Labels := by
      have ha : raw27111step3 = raw27111step2 := by apply Matrix.ext; unfold raw27111step3 raw27111step2; decide +kernel
      have hl : raw27111step2Labels = labelEmbedding1 ∘ raw27111step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27111step2 raw27111step2Labels raw27111step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1512 node1512Labels := by rfl

def raw27112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27112Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw27112step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27112step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27112step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27112step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27112 raw27112Labels = mixedMoment B node1668 node1668Labels := by
  calc
    mixedMoment B raw27112 raw27112Labels = mixedMoment B raw27112step0 raw27112step0Labels := by
      have ha : raw27112step0 = (fun i j => raw27112 (permutation175 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27112step0 raw27112; decide +kernel
      have hl : raw27112step0Labels = raw27112Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27112 raw27112Labels permutation175 permutation7
    mixedMoment B raw27112step0 raw27112step0Labels = mixedMoment B raw27112step1 raw27112step1Labels := by
      have ha : raw27112step1 = -raw27112step0 := by apply Matrix.ext; change ∀ i j, raw27112step1 i j = -(raw27112step0 i j); unfold raw27112step1 raw27112step0; decide +kernel
      have hl : raw27112step1Labels = raw27112step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27112step1 raw27112step1Labels = mixedMoment B raw27112step2 raw27112step2Labels := by
      have ha : raw27112step2 = raw27112step1 := by apply Matrix.ext; unfold raw27112step2 raw27112step1; decide +kernel
      have hl : raw27112step1Labels = labelEmbedding1 ∘ raw27112step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27112step1 raw27112step1Labels raw27112step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1668 node1668Labels := by rfl

def raw27113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27113Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27113step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw27113step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27113step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27113step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27113step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27113 raw27113Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw27113 raw27113Labels = mixedMoment B raw27113step0 raw27113step0Labels := by
      have hz : ∀ j, raw27113 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27113step0 = (fun i j => raw27113 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27113step0 raw27113; decide +kernel
      have hl : raw27113step0Labels = raw27113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27113 raw27113Labels permutation265 hz
    mixedMoment B raw27113step0 raw27113step0Labels = mixedMoment B raw27113step1 raw27113step1Labels := by
      have ha : raw27113step1 = (fun i j => raw27113step0 (permutation55 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27113step1 raw27113step0; decide +kernel
      have hl : raw27113step1Labels = raw27113step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27113step0 raw27113step0Labels permutation55 permutation7
    mixedMoment B raw27113step1 raw27113step1Labels = mixedMoment B raw27113step2 raw27113step2Labels := by
      have ha : raw27113step2 = -raw27113step1 := by apply Matrix.ext; change ∀ i j, raw27113step2 i j = -(raw27113step1 i j); unfold raw27113step2 raw27113step1; decide +kernel
      have hl : raw27113step2Labels = raw27113step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27113step2 raw27113step2Labels = mixedMoment B raw27113step3 raw27113step3Labels := by
      have ha : raw27113step3 = raw27113step2 := by apply Matrix.ext; unfold raw27113step3 raw27113step2; decide +kernel
      have hl : raw27113step2Labels = labelEmbedding1 ∘ raw27113step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27113step2 raw27113step2Labels raw27113step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1715 node1715Labels := by rfl

def raw27114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27114Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw27114step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw27114step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27114step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw27114step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27114step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw27114step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27114 raw27114Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw27114 raw27114Labels = mixedMoment B raw27114step0 raw27114step0Labels := by
      have hz : ∀ j, raw27114 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27114step0 = (fun i j => raw27114 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27114step0 raw27114; decide +kernel
      have hl : raw27114step0Labels = raw27114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27114 raw27114Labels permutation265 hz
    mixedMoment B raw27114step0 raw27114step0Labels = mixedMoment B raw27114step1 raw27114step1Labels := by
      have ha : raw27114step1 = (fun i j => raw27114step0 (permutation55 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27114step1 raw27114step0; decide +kernel
      have hl : raw27114step1Labels = raw27114step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27114step0 raw27114step0Labels permutation55 permutation7
    mixedMoment B raw27114step1 raw27114step1Labels = mixedMoment B raw27114step2 raw27114step2Labels := by
      have ha : raw27114step2 = -raw27114step1 := by apply Matrix.ext; change ∀ i j, raw27114step2 i j = -(raw27114step1 i j); unfold raw27114step2 raw27114step1; decide +kernel
      have hl : raw27114step2Labels = raw27114step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27114step2 raw27114step2Labels = mixedMoment B raw27114step3 raw27114step3Labels := by
      have ha : raw27114step3 = raw27114step2 := by apply Matrix.ext; unfold raw27114step3 raw27114step2; decide +kernel
      have hl : raw27114step2Labels = labelEmbedding1 ∘ raw27114step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27114step2 raw27114step2Labels raw27114step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

def raw27115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw27115Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27115step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27115step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27115step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw27115step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27115step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27115step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27115step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27115step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27115 raw27115Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw27115 raw27115Labels = mixedMoment B raw27115step0 raw27115step0Labels := by
      have hz : ∀ j, raw27115 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw27115step0 = (fun i j => raw27115 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw27115step0 raw27115; decide +kernel
      have hl : raw27115step0Labels = raw27115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27115 raw27115Labels permutation590 hz
    mixedMoment B raw27115step0 raw27115step0Labels = mixedMoment B raw27115step1 raw27115step1Labels := by
      have hz : ∀ j, raw27115step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27115step1 = (fun i j => raw27115step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27115step1 raw27115step0; decide +kernel
      have hl : raw27115step1Labels = raw27115step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27115step0 raw27115step0Labels permutation56 hz
    mixedMoment B raw27115step1 raw27115step1Labels = mixedMoment B raw27115step2 raw27115step2Labels := by
      have ha : raw27115step2 = (fun i j => raw27115step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27115step2 raw27115step1; decide +kernel
      have hl : raw27115step2Labels = raw27115step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27115step1 raw27115step1Labels permutation13 permutation7
    mixedMoment B raw27115step2 raw27115step2Labels = mixedMoment B raw27115step3 raw27115step3Labels := by
      have ha : raw27115step3 = -raw27115step2 := by apply Matrix.ext; change ∀ i j, raw27115step3 i j = -(raw27115step2 i j); unfold raw27115step3 raw27115step2; decide +kernel
      have hl : raw27115step3Labels = raw27115step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27115step3 raw27115step3Labels = mixedMoment B raw27115step4 raw27115step4Labels := by
      have ha : raw27115step4 = raw27115step3 := by apply Matrix.ext; unfold raw27115step4 raw27115step3; decide +kernel
      have hl : raw27115step3Labels = labelEmbedding1 ∘ raw27115step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27115step3 raw27115step3Labels raw27115step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1739 node1739Labels := by rfl

def raw27116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27116Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27116step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw27116step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27116step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27116step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27116step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27116step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27116 raw27116Labels = mixedMoment B node1512 node1512Labels := by
  calc
    mixedMoment B raw27116 raw27116Labels = mixedMoment B raw27116step0 raw27116step0Labels := by
      have hz : ∀ j, raw27116 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27116step0 = (fun i j => raw27116 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27116step0 raw27116; decide +kernel
      have hl : raw27116step0Labels = raw27116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27116 raw27116Labels permutation265 hz
    mixedMoment B raw27116step0 raw27116step0Labels = mixedMoment B raw27116step1 raw27116step1Labels := by
      have ha : raw27116step1 = (fun i j => raw27116step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27116step1 raw27116step0; decide +kernel
      have hl : raw27116step1Labels = raw27116step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27116step0 raw27116step0Labels permutation49 permutation7
    mixedMoment B raw27116step1 raw27116step1Labels = mixedMoment B raw27116step2 raw27116step2Labels := by
      have ha : raw27116step2 = -raw27116step1 := by apply Matrix.ext; change ∀ i j, raw27116step2 i j = -(raw27116step1 i j); unfold raw27116step2 raw27116step1; decide +kernel
      have hl : raw27116step2Labels = raw27116step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27116step2 raw27116step2Labels = mixedMoment B raw27116step3 raw27116step3Labels := by
      have ha : raw27116step3 = raw27116step2 := by apply Matrix.ext; unfold raw27116step3 raw27116step2; decide +kernel
      have hl : raw27116step2Labels = labelEmbedding1 ∘ raw27116step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27116step2 raw27116step2Labels raw27116step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1512 node1512Labels := by rfl

def raw27117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27117Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27117step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw27117step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27117step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27117step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27117step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27117step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27117 raw27117Labels = mixedMoment B node1668 node1668Labels := by
  calc
    mixedMoment B raw27117 raw27117Labels = mixedMoment B raw27117step0 raw27117step0Labels := by
      have ha : raw27117step0 = (fun i j => raw27117 (permutation169 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27117step0 raw27117; decide +kernel
      have hl : raw27117step0Labels = raw27117Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27117 raw27117Labels permutation169 permutation7
    mixedMoment B raw27117step0 raw27117step0Labels = mixedMoment B raw27117step1 raw27117step1Labels := by
      have ha : raw27117step1 = -raw27117step0 := by apply Matrix.ext; change ∀ i j, raw27117step1 i j = -(raw27117step0 i j); unfold raw27117step1 raw27117step0; decide +kernel
      have hl : raw27117step1Labels = raw27117step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27117step1 raw27117step1Labels = mixedMoment B raw27117step2 raw27117step2Labels := by
      have ha : raw27117step2 = raw27117step1 := by apply Matrix.ext; unfold raw27117step2 raw27117step1; decide +kernel
      have hl : raw27117step1Labels = labelEmbedding1 ∘ raw27117step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27117step1 raw27117step1Labels raw27117step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1668 node1668Labels := by rfl

def raw27118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27118Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27118step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw27118step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27118step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27118step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27118step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27118 raw27118Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw27118 raw27118Labels = mixedMoment B raw27118step0 raw27118step0Labels := by
      have hz : ∀ j, raw27118 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27118step0 = (fun i j => raw27118 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27118step0 raw27118; decide +kernel
      have hl : raw27118step0Labels = raw27118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27118 raw27118Labels permutation265 hz
    mixedMoment B raw27118step0 raw27118step0Labels = mixedMoment B raw27118step1 raw27118step1Labels := by
      have ha : raw27118step1 = (fun i j => raw27118step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27118step1 raw27118step0; decide +kernel
      have hl : raw27118step1Labels = raw27118step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27118step0 raw27118step0Labels permutation49 permutation7
    mixedMoment B raw27118step1 raw27118step1Labels = mixedMoment B raw27118step2 raw27118step2Labels := by
      have ha : raw27118step2 = -raw27118step1 := by apply Matrix.ext; change ∀ i j, raw27118step2 i j = -(raw27118step1 i j); unfold raw27118step2 raw27118step1; decide +kernel
      have hl : raw27118step2Labels = raw27118step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27118step2 raw27118step2Labels = mixedMoment B raw27118step3 raw27118step3Labels := by
      have ha : raw27118step3 = raw27118step2 := by apply Matrix.ext; unfold raw27118step3 raw27118step2; decide +kernel
      have hl : raw27118step2Labels = labelEmbedding1 ∘ raw27118step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27118step2 raw27118step2Labels raw27118step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1715 node1715Labels := by rfl

def raw27119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27119Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw27119step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw27119step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27119step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw27119step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27119step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw27119step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27119 raw27119Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw27119 raw27119Labels = mixedMoment B raw27119step0 raw27119step0Labels := by
      have hz : ∀ j, raw27119 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27119step0 = (fun i j => raw27119 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27119step0 raw27119; decide +kernel
      have hl : raw27119step0Labels = raw27119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27119 raw27119Labels permutation265 hz
    mixedMoment B raw27119step0 raw27119step0Labels = mixedMoment B raw27119step1 raw27119step1Labels := by
      have ha : raw27119step1 = (fun i j => raw27119step0 (permutation49 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27119step1 raw27119step0; decide +kernel
      have hl : raw27119step1Labels = raw27119step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27119step0 raw27119step0Labels permutation49 permutation7
    mixedMoment B raw27119step1 raw27119step1Labels = mixedMoment B raw27119step2 raw27119step2Labels := by
      have ha : raw27119step2 = -raw27119step1 := by apply Matrix.ext; change ∀ i j, raw27119step2 i j = -(raw27119step1 i j); unfold raw27119step2 raw27119step1; decide +kernel
      have hl : raw27119step2Labels = raw27119step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27119step2 raw27119step2Labels = mixedMoment B raw27119step3 raw27119step3Labels := by
      have ha : raw27119step3 = raw27119step2 := by apply Matrix.ext; unfold raw27119step3 raw27119step2; decide +kernel
      have hl : raw27119step2Labels = labelEmbedding1 ∘ raw27119step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27119step2 raw27119step2Labels raw27119step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

def raw27120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw27120Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27120step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw27120step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw27120step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw27120step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27120step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27120step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw27120step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw27120step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical27120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27120 raw27120Labels = mixedMoment B node1739 node1739Labels := by
  calc
    mixedMoment B raw27120 raw27120Labels = mixedMoment B raw27120step0 raw27120step0Labels := by
      have hz : ∀ j, raw27120 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw27120step0 = (fun i j => raw27120 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw27120step0 raw27120; decide +kernel
      have hl : raw27120step0Labels = raw27120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27120 raw27120Labels permutation520 hz
    mixedMoment B raw27120step0 raw27120step0Labels = mixedMoment B raw27120step1 raw27120step1Labels := by
      have hz : ∀ j, raw27120step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27120step1 = (fun i j => raw27120step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27120step1 raw27120step0; decide +kernel
      have hl : raw27120step1Labels = raw27120step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27120step0 raw27120step0Labels permutation56 hz
    mixedMoment B raw27120step1 raw27120step1Labels = mixedMoment B raw27120step2 raw27120step2Labels := by
      have ha : raw27120step2 = (fun i j => raw27120step1 (permutation13 i) (permutation7 j)) := by apply Matrix.ext; unfold raw27120step2 raw27120step1; decide +kernel
      have hl : raw27120step2Labels = raw27120step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27120step1 raw27120step1Labels permutation13 permutation7
    mixedMoment B raw27120step2 raw27120step2Labels = mixedMoment B raw27120step3 raw27120step3Labels := by
      have ha : raw27120step3 = -raw27120step2 := by apply Matrix.ext; change ∀ i j, raw27120step3 i j = -(raw27120step2 i j); unfold raw27120step3 raw27120step2; decide +kernel
      have hl : raw27120step3Labels = raw27120step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw27120step3 raw27120step3Labels = mixedMoment B raw27120step4 raw27120step4Labels := by
      have ha : raw27120step4 = raw27120step3 := by apply Matrix.ext; unfold raw27120step4 raw27120step3; decide +kernel
      have hl : raw27120step3Labels = labelEmbedding1 ∘ raw27120step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27120step3 raw27120step3Labels raw27120step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1739 node1739Labels := by rfl

def raw27121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27121step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27121step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27121step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27121 raw27121Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw27121 raw27121Labels = mixedMoment B raw27121step0 raw27121step0Labels := by
      have ha : raw27121step0 = (fun i j => raw27121 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27121step0 raw27121; decide +kernel
      have hl : raw27121step0Labels = raw27121Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27121 raw27121Labels permutation169 permutation3
    mixedMoment B raw27121step0 raw27121step0Labels = mixedMoment B raw27121step1 raw27121step1Labels := by
      have ha : raw27121step1 = raw27121step0 := by apply Matrix.ext; unfold raw27121step1 raw27121step0; decide +kernel
      have hl : raw27121step0Labels = labelEmbedding6 ∘ raw27121step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27121step0 raw27121step0Labels raw27121step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5098 node5098Labels := by rfl

def raw27122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw27122step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw27122step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27122 raw27122Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw27122 raw27122Labels = mixedMoment B raw27122step0 raw27122step0Labels := by
      have hz : ∀ j, raw27122 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27122step0 = (fun i j => raw27122 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27122step0 raw27122; decide +kernel
      have hl : raw27122step0Labels = raw27122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27122 raw27122Labels permutation265 hz
    mixedMoment B raw27122step0 raw27122step0Labels = mixedMoment B raw27122step1 raw27122step1Labels := by
      have ha : raw27122step1 = (fun i j => raw27122step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27122step1 raw27122step0; decide +kernel
      have hl : raw27122step1Labels = raw27122step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27122step0 raw27122step0Labels permutation35 permutation3
    mixedMoment B raw27122step1 raw27122step1Labels = mixedMoment B raw27122step2 raw27122step2Labels := by
      have ha : raw27122step2 = raw27122step1 := by apply Matrix.ext; unfold raw27122step2 raw27122step1; decide +kernel
      have hl : raw27122step1Labels = labelEmbedding6 ∘ raw27122step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27122step1 raw27122step1Labels raw27122step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw27123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw27123step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27123step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw27123step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27123step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw27123step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27123step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw27123step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27123 raw27123Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw27123 raw27123Labels = mixedMoment B raw27123step0 raw27123step0Labels := by
      have hz : ∀ j, raw27123 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27123step0 = (fun i j => raw27123 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27123step0 raw27123; decide +kernel
      have hl : raw27123step0Labels = raw27123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27123 raw27123Labels permutation434 hz
    mixedMoment B raw27123step0 raw27123step0Labels = mixedMoment B raw27123step1 raw27123step1Labels := by
      have hz : ∀ j, raw27123step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27123step1 = (fun i j => raw27123step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27123step1 raw27123step0; decide +kernel
      have hl : raw27123step1Labels = raw27123step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27123step0 raw27123step0Labels permutation56 hz
    mixedMoment B raw27123step1 raw27123step1Labels = mixedMoment B raw27123step2 raw27123step2Labels := by
      have ha : raw27123step2 = (fun i j => raw27123step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27123step2 raw27123step1; decide +kernel
      have hl : raw27123step2Labels = raw27123step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27123step1 raw27123step1Labels permutation11 permutation3
    mixedMoment B raw27123step2 raw27123step2Labels = mixedMoment B raw27123step3 raw27123step3Labels := by
      have ha : raw27123step3 = raw27123step2 := by apply Matrix.ext; unfold raw27123step3 raw27123step2; decide +kernel
      have hl : raw27123step2Labels = labelEmbedding6 ∘ raw27123step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27123step2 raw27123step2Labels raw27123step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw27124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw27124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw27124step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27124step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27124step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27124 raw27124Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw27124 raw27124Labels = mixedMoment B raw27124step0 raw27124step0Labels := by
      have hz : ∀ j, raw27124 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27124step0 = (fun i j => raw27124 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27124step0 raw27124; decide +kernel
      have hl : raw27124step0Labels = raw27124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27124 raw27124Labels permutation265 hz
    mixedMoment B raw27124step0 raw27124step0Labels = mixedMoment B raw27124step1 raw27124step1Labels := by
      have ha : raw27124step1 = (fun i j => raw27124step0 (permutation49 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27124step1 raw27124step0; decide +kernel
      have hl : raw27124step1Labels = raw27124step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27124step0 raw27124step0Labels permutation49 permutation3
    mixedMoment B raw27124step1 raw27124step1Labels = mixedMoment B raw27124step2 raw27124step2Labels := by
      have ha : raw27124step2 = raw27124step1 := by apply Matrix.ext; unfold raw27124step2 raw27124step1; decide +kernel
      have hl : raw27124step1Labels = labelEmbedding6 ∘ raw27124step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27124step1 raw27124step1Labels raw27124step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw27125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw27125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw27125step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27125step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27125step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27125step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27125step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27125 raw27125Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw27125 raw27125Labels = mixedMoment B raw27125step0 raw27125step0Labels := by
      have hz : ∀ j, raw27125 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27125step0 = (fun i j => raw27125 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27125step0 raw27125; decide +kernel
      have hl : raw27125step0Labels = raw27125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27125 raw27125Labels permutation265 hz
    mixedMoment B raw27125step0 raw27125step0Labels = mixedMoment B raw27125step1 raw27125step1Labels := by
      have ha : raw27125step1 = (fun i j => raw27125step0 (permutation55 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27125step1 raw27125step0; decide +kernel
      have hl : raw27125step1Labels = raw27125step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27125step0 raw27125step0Labels permutation55 permutation3
    mixedMoment B raw27125step1 raw27125step1Labels = mixedMoment B raw27125step2 raw27125step2Labels := by
      have ha : raw27125step2 = raw27125step1 := by apply Matrix.ext; unfold raw27125step2 raw27125step1; decide +kernel
      have hl : raw27125step1Labels = labelEmbedding6 ∘ raw27125step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27125step1 raw27125step1Labels raw27125step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw27126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27126step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27126step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27126step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27126step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27126 raw27126Labels = mixedMoment B node4113 node4113Labels := by
  calc
    mixedMoment B raw27126 raw27126Labels = mixedMoment B raw27126step0 raw27126step0Labels := by
      have ha : raw27126step0 = (fun i j => raw27126 (permutation241 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27126step0 raw27126; decide +kernel
      have hl : raw27126step0Labels = raw27126Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27126 raw27126Labels permutation241 permutation3
    mixedMoment B raw27126step0 raw27126step0Labels = mixedMoment B raw27126step1 raw27126step1Labels := by
      have ha : raw27126step1 = raw27126step0 := by apply Matrix.ext; unfold raw27126step1 raw27126step0; decide +kernel
      have hl : raw27126step0Labels = labelEmbedding6 ∘ raw27126step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27126step0 raw27126step0Labels raw27126step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4113 node4113Labels := by rfl

def raw27127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27127step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27127step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27127step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27127 raw27127Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw27127 raw27127Labels = mixedMoment B raw27127step0 raw27127step0Labels := by
      have ha : raw27127step0 = (fun i j => raw27127 (permutation192 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27127step0 raw27127; decide +kernel
      have hl : raw27127step0Labels = raw27127Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27127 raw27127Labels permutation192 permutation3
    mixedMoment B raw27127step0 raw27127step0Labels = mixedMoment B raw27127step1 raw27127step1Labels := by
      have ha : raw27127step1 = raw27127step0 := by apply Matrix.ext; unfold raw27127step1 raw27127step0; decide +kernel
      have hl : raw27127step0Labels = labelEmbedding6 ∘ raw27127step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27127step0 raw27127step0Labels raw27127step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw27128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw27128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27128step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw27128step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27128 raw27128Labels = mixedMoment B node4495 node4495Labels := by
  calc
    mixedMoment B raw27128 raw27128Labels = mixedMoment B raw27128step0 raw27128step0Labels := by
      have hz : ∀ j, raw27128 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27128step0 = (fun i j => raw27128 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27128step0 raw27128; decide +kernel
      have hl : raw27128step0Labels = raw27128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27128 raw27128Labels permutation434 hz
    mixedMoment B raw27128step0 raw27128step0Labels = mixedMoment B raw27128step1 raw27128step1Labels := by
      have ha : raw27128step1 = (fun i j => raw27128step0 (permutation48 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27128step1 raw27128step0; decide +kernel
      have hl : raw27128step1Labels = raw27128step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27128step0 raw27128step0Labels permutation48 permutation3
    mixedMoment B raw27128step1 raw27128step1Labels = mixedMoment B raw27128step2 raw27128step2Labels := by
      have ha : raw27128step2 = raw27128step1 := by apply Matrix.ext; unfold raw27128step2 raw27128step1; decide +kernel
      have hl : raw27128step1Labels = labelEmbedding6 ∘ raw27128step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27128step1 raw27128step1Labels raw27128step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4495 node4495Labels := by rfl

def raw27129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw27129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27129step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27129step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27129step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27129 raw27129Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw27129 raw27129Labels = mixedMoment B raw27129step0 raw27129step0Labels := by
      have ha : raw27129step0 = (fun i j => raw27129 (permutation241 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27129step0 raw27129; decide +kernel
      have hl : raw27129step0Labels = raw27129Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27129 raw27129Labels permutation241 permutation3
    mixedMoment B raw27129step0 raw27129step0Labels = mixedMoment B raw27129step1 raw27129step1Labels := by
      have ha : raw27129step1 = raw27129step0 := by apply Matrix.ext; unfold raw27129step1 raw27129step0; decide +kernel
      have hl : raw27129step0Labels = labelEmbedding6 ∘ raw27129step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27129step0 raw27129step0Labels raw27129step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

def raw27130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw27130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27130step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27130step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27130step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw27130step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27130 raw27130Labels = mixedMoment B node4417 node4417Labels := by
  calc
    mixedMoment B raw27130 raw27130Labels = mixedMoment B raw27130step0 raw27130step0Labels := by
      have ha : raw27130step0 = (fun i j => raw27130 (permutation261 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27130step0 raw27130; decide +kernel
      have hl : raw27130step0Labels = raw27130Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27130 raw27130Labels permutation261 permutation3
    mixedMoment B raw27130step0 raw27130step0Labels = mixedMoment B raw27130step1 raw27130step1Labels := by
      have ha : raw27130step1 = raw27130step0 := by apply Matrix.ext; unfold raw27130step1 raw27130step0; decide +kernel
      have hl : raw27130step0Labels = labelEmbedding6 ∘ raw27130step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27130step0 raw27130step0Labels raw27130step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4417 node4417Labels := by rfl

def raw27131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27131step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27131step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27131step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27131step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27131 raw27131Labels = mixedMoment B node4114 node4114Labels := by
  calc
    mixedMoment B raw27131 raw27131Labels = mixedMoment B raw27131step0 raw27131step0Labels := by
      have hz : ∀ j, raw27131 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27131step0 = (fun i j => raw27131 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27131step0 raw27131; decide +kernel
      have hl : raw27131step0Labels = raw27131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27131 raw27131Labels permutation265 hz
    mixedMoment B raw27131step0 raw27131step0Labels = mixedMoment B raw27131step1 raw27131step1Labels := by
      have ha : raw27131step1 = (fun i j => raw27131step0 (permutation49 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27131step1 raw27131step0; decide +kernel
      have hl : raw27131step1Labels = raw27131step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27131step0 raw27131step0Labels permutation49 permutation3
    mixedMoment B raw27131step1 raw27131step1Labels = mixedMoment B raw27131step2 raw27131step2Labels := by
      have ha : raw27131step2 = raw27131step1 := by apply Matrix.ext; unfold raw27131step2 raw27131step1; decide +kernel
      have hl : raw27131step1Labels = labelEmbedding6 ∘ raw27131step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27131step1 raw27131step1Labels raw27131step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4114 node4114Labels := by rfl

def raw27132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27132step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27132step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27132 raw27132Labels = mixedMoment B node4297 node4297Labels := by
  calc
    mixedMoment B raw27132 raw27132Labels = mixedMoment B raw27132step0 raw27132step0Labels := by
      have ha : raw27132step0 = (fun i j => raw27132 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27132step0 raw27132; decide +kernel
      have hl : raw27132step0Labels = raw27132Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27132 raw27132Labels permutation169 permutation3
    mixedMoment B raw27132step0 raw27132step0Labels = mixedMoment B raw27132step1 raw27132step1Labels := by
      have ha : raw27132step1 = raw27132step0 := by apply Matrix.ext; unfold raw27132step1 raw27132step0; decide +kernel
      have hl : raw27132step0Labels = labelEmbedding6 ∘ raw27132step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27132step0 raw27132step0Labels raw27132step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4297 node4297Labels := by rfl

def raw27133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -3, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw27133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw27133step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27133step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw27133step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27133step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw27133step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27133step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw27133step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27133 raw27133Labels = mixedMoment B node4496 node4496Labels := by
  calc
    mixedMoment B raw27133 raw27133Labels = mixedMoment B raw27133step0 raw27133step0Labels := by
      have hz : ∀ j, raw27133 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw27133step0 = (fun i j => raw27133 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw27133step0 raw27133; decide +kernel
      have hl : raw27133step0Labels = raw27133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27133 raw27133Labels permutation434 hz
    mixedMoment B raw27133step0 raw27133step0Labels = mixedMoment B raw27133step1 raw27133step1Labels := by
      have hz : ∀ j, raw27133step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw27133step1 = (fun i j => raw27133step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw27133step1 raw27133step0; decide +kernel
      have hl : raw27133step1Labels = raw27133step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27133step0 raw27133step0Labels permutation56 hz
    mixedMoment B raw27133step1 raw27133step1Labels = mixedMoment B raw27133step2 raw27133step2Labels := by
      have ha : raw27133step2 = (fun i j => raw27133step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27133step2 raw27133step1; decide +kernel
      have hl : raw27133step2Labels = raw27133step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27133step1 raw27133step1Labels permutation11 permutation3
    mixedMoment B raw27133step2 raw27133step2Labels = mixedMoment B raw27133step3 raw27133step3Labels := by
      have ha : raw27133step3 = raw27133step2 := by apply Matrix.ext; unfold raw27133step3 raw27133step2; decide +kernel
      have hl : raw27133step2Labels = labelEmbedding6 ∘ raw27133step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27133step2 raw27133step2Labels raw27133step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4496 node4496Labels := by rfl

def raw27134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw27134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw27134step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27134step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27134step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27134step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27134 raw27134Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw27134 raw27134Labels = mixedMoment B raw27134step0 raw27134step0Labels := by
      have hz : ∀ j, raw27134 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27134step0 = (fun i j => raw27134 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27134step0 raw27134; decide +kernel
      have hl : raw27134step0Labels = raw27134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27134 raw27134Labels permutation265 hz
    mixedMoment B raw27134step0 raw27134step0Labels = mixedMoment B raw27134step1 raw27134step1Labels := by
      have ha : raw27134step1 = (fun i j => raw27134step0 (permutation49 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27134step1 raw27134step0; decide +kernel
      have hl : raw27134step1Labels = raw27134step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27134step0 raw27134step0Labels permutation49 permutation3
    mixedMoment B raw27134step1 raw27134step1Labels = mixedMoment B raw27134step2 raw27134step2Labels := by
      have ha : raw27134step2 = raw27134step1 := by apply Matrix.ext; unfold raw27134step2 raw27134step1; decide +kernel
      have hl : raw27134step1Labels = labelEmbedding6 ∘ raw27134step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27134step1 raw27134step1Labels raw27134step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4418 node4418Labels := by rfl

def raw27135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw27135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw27135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw27135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27135step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw27135step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw27135step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical27135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw27135 raw27135Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw27135 raw27135Labels = mixedMoment B raw27135step0 raw27135step0Labels := by
      have hz : ∀ j, raw27135 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw27135step0 = (fun i j => raw27135 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw27135step0 raw27135; decide +kernel
      have hl : raw27135step0Labels = raw27135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw27135 raw27135Labels permutation265 hz
    mixedMoment B raw27135step0 raw27135step0Labels = mixedMoment B raw27135step1 raw27135step1Labels := by
      have ha : raw27135step1 = (fun i j => raw27135step0 (permutation55 i) (permutation3 j)) := by apply Matrix.ext; unfold raw27135step1 raw27135step0; decide +kernel
      have hl : raw27135step1Labels = raw27135step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw27135step0 raw27135step0Labels permutation55 permutation3
    mixedMoment B raw27135step1 raw27135step1Labels = mixedMoment B raw27135step2 raw27135step2Labels := by
      have ha : raw27135step2 = raw27135step1 := by apply Matrix.ext; unfold raw27135step2 raw27135step1; decide +kernel
      have hl : raw27135step1Labels = labelEmbedding6 ∘ raw27135step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw27135step1 raw27135step1Labels raw27135step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4418 node4418Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
