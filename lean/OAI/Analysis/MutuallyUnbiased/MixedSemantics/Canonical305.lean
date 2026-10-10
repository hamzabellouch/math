import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw39040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw39040Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw39040step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39040step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw39040step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39040step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw39040step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39040 raw39040Labels = mixedMoment B node3332 node3332Labels := by
  calc
    mixedMoment B raw39040 raw39040Labels = mixedMoment B raw39040step0 raw39040step0Labels := by
      have ha : raw39040step0 = (fun i j => raw39040 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39040step0 raw39040; decide +kernel
      have hl : raw39040step0Labels = raw39040Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39040 raw39040Labels permutation152 permutation7
    mixedMoment B raw39040step0 raw39040step0Labels = mixedMoment B raw39040step1 raw39040step1Labels := by
      have ha : raw39040step1 = -raw39040step0 := by apply Matrix.ext; change ∀ i j, raw39040step1 i j = -(raw39040step0 i j); unfold raw39040step1 raw39040step0; decide +kernel
      have hl : raw39040step1Labels = raw39040step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39040step1 raw39040step1Labels = mixedMoment B raw39040step2 raw39040step2Labels := by
      have ha : raw39040step2 = raw39040step1 := by apply Matrix.ext; unfold raw39040step2 raw39040step1; decide +kernel
      have hl : raw39040step1Labels = labelEmbedding4 ∘ raw39040step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39040step1 raw39040step1Labels raw39040step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3332 node3332Labels := by rfl

def raw39041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw39041Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw39041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39041 raw39041Labels = mixedMoment B node2374 node2374Labels := by
  calc
    mixedMoment B raw39041 raw39041Labels = mixedMoment B raw39041step0 raw39041step0Labels := by
      have ha : raw39041step0 = raw39041 := by apply Matrix.ext; unfold raw39041step0 raw39041; decide +kernel
      have hl : raw39041Labels = labelEmbedding2 ∘ raw39041step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39041 raw39041Labels raw39041step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2374 node2374Labels := by rfl

def raw39042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw39042Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw39042step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39042step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw39042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39042 raw39042Labels = mixedMoment B node2413 node2413Labels := by
  calc
    mixedMoment B raw39042 raw39042Labels = mixedMoment B raw39042step0 raw39042step0Labels := by
      have ha : raw39042step0 = (fun i j => raw39042 (permutation664 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39042step0 raw39042; decide +kernel
      have hl : raw39042step0Labels = raw39042Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39042 raw39042Labels permutation664 permutation7
    mixedMoment B raw39042step0 raw39042step0Labels = mixedMoment B raw39042step1 raw39042step1Labels := by
      have ha : raw39042step1 = raw39042step0 := by apply Matrix.ext; unfold raw39042step1 raw39042step0; decide +kernel
      have hl : raw39042step0Labels = labelEmbedding4 ∘ raw39042step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39042step0 raw39042step0Labels raw39042step1Labels labelEmbedding4 hl
    _ = mixedMoment B node2413 node2413Labels := by rfl

def raw39043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw39043Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw39043step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39043 raw39043Labels = mixedMoment B node2375 node2375Labels := by
  calc
    mixedMoment B raw39043 raw39043Labels = mixedMoment B raw39043step0 raw39043step0Labels := by
      have ha : raw39043step0 = raw39043 := by apply Matrix.ext; unfold raw39043step0 raw39043; decide +kernel
      have hl : raw39043Labels = labelEmbedding2 ∘ raw39043step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39043 raw39043Labels raw39043step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2375 node2375Labels := by rfl

def raw39044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw39044Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw39044step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39044step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw39044step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39044step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw39044step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39044 raw39044Labels = mixedMoment B node3333 node3333Labels := by
  calc
    mixedMoment B raw39044 raw39044Labels = mixedMoment B raw39044step0 raw39044step0Labels := by
      have ha : raw39044step0 = (fun i j => raw39044 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39044step0 raw39044; decide +kernel
      have hl : raw39044step0Labels = raw39044Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39044 raw39044Labels permutation152 permutation7
    mixedMoment B raw39044step0 raw39044step0Labels = mixedMoment B raw39044step1 raw39044step1Labels := by
      have ha : raw39044step1 = -raw39044step0 := by apply Matrix.ext; change ∀ i j, raw39044step1 i j = -(raw39044step0 i j); unfold raw39044step1 raw39044step0; decide +kernel
      have hl : raw39044step1Labels = raw39044step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39044step1 raw39044step1Labels = mixedMoment B raw39044step2 raw39044step2Labels := by
      have ha : raw39044step2 = raw39044step1 := by apply Matrix.ext; unfold raw39044step2 raw39044step1; decide +kernel
      have hl : raw39044step1Labels = labelEmbedding4 ∘ raw39044step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39044step1 raw39044step1Labels raw39044step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3333 node3333Labels := by rfl

def raw39045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39045Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39045 raw39045Labels = mixedMoment B node2382 node2382Labels := by
  calc
    mixedMoment B raw39045 raw39045Labels = mixedMoment B raw39045step0 raw39045step0Labels := by
      have ha : raw39045step0 = raw39045 := by apply Matrix.ext; unfold raw39045step0 raw39045; decide +kernel
      have hl : raw39045Labels = labelEmbedding2 ∘ raw39045step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39045 raw39045Labels raw39045step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2382 node2382Labels := by rfl

def raw39046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39046Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw39046step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39046step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39046step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39046step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39046 raw39046Labels = mixedMoment B node3340 node3340Labels := by
  calc
    mixedMoment B raw39046 raw39046Labels = mixedMoment B raw39046step0 raw39046step0Labels := by
      have ha : raw39046step0 = (fun i j => raw39046 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39046step0 raw39046; decide +kernel
      have hl : raw39046step0Labels = raw39046Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39046 raw39046Labels permutation158 permutation7
    mixedMoment B raw39046step0 raw39046step0Labels = mixedMoment B raw39046step1 raw39046step1Labels := by
      have ha : raw39046step1 = -raw39046step0 := by apply Matrix.ext; change ∀ i j, raw39046step1 i j = -(raw39046step0 i j); unfold raw39046step1 raw39046step0; decide +kernel
      have hl : raw39046step1Labels = raw39046step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39046step1 raw39046step1Labels = mixedMoment B raw39046step2 raw39046step2Labels := by
      have ha : raw39046step2 = raw39046step1 := by apply Matrix.ext; unfold raw39046step2 raw39046step1; decide +kernel
      have hl : raw39046step1Labels = labelEmbedding4 ∘ raw39046step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39046step1 raw39046step1Labels raw39046step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3340 node3340Labels := by rfl

def raw39047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39047Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39047step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39047 raw39047Labels = mixedMoment B node2383 node2383Labels := by
  calc
    mixedMoment B raw39047 raw39047Labels = mixedMoment B raw39047step0 raw39047step0Labels := by
      have ha : raw39047step0 = raw39047 := by apply Matrix.ext; unfold raw39047step0 raw39047; decide +kernel
      have hl : raw39047Labels = labelEmbedding2 ∘ raw39047step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39047 raw39047Labels raw39047step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2383 node2383Labels := by rfl

def raw39048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39048Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw39048step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39048step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39048step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39048step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39048step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39048 raw39048Labels = mixedMoment B node3352 node3352Labels := by
  calc
    mixedMoment B raw39048 raw39048Labels = mixedMoment B raw39048step0 raw39048step0Labels := by
      have ha : raw39048step0 = (fun i j => raw39048 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39048step0 raw39048; decide +kernel
      have hl : raw39048step0Labels = raw39048Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39048 raw39048Labels permutation152 permutation7
    mixedMoment B raw39048step0 raw39048step0Labels = mixedMoment B raw39048step1 raw39048step1Labels := by
      have ha : raw39048step1 = -raw39048step0 := by apply Matrix.ext; change ∀ i j, raw39048step1 i j = -(raw39048step0 i j); unfold raw39048step1 raw39048step0; decide +kernel
      have hl : raw39048step1Labels = raw39048step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39048step1 raw39048step1Labels = mixedMoment B raw39048step2 raw39048step2Labels := by
      have ha : raw39048step2 = raw39048step1 := by apply Matrix.ext; unfold raw39048step2 raw39048step1; decide +kernel
      have hl : raw39048step1Labels = labelEmbedding4 ∘ raw39048step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39048step1 raw39048step1Labels raw39048step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3352 node3352Labels := by rfl

def raw39049 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw39049Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw39049step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39049 raw39049Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw39049 raw39049Labels = mixedMoment B raw39049step0 raw39049step0Labels := by
      have ha : raw39049step0 = raw39049 := by apply Matrix.ext; unfold raw39049step0 raw39049; decide +kernel
      have hl : raw39049Labels = labelEmbedding2 ∘ raw39049step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39049 raw39049Labels raw39049step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2385 node2385Labels := by rfl

def raw39050 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw39050Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw39050step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw39050step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39050step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw39050step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39050 raw39050Labels = mixedMoment B node3353 node3353Labels := by
  calc
    mixedMoment B raw39050 raw39050Labels = mixedMoment B raw39050step0 raw39050step0Labels := by
      have ha : raw39050step0 = (fun i j => raw39050 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39050step0 raw39050; decide +kernel
      have hl : raw39050step0Labels = raw39050Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39050 raw39050Labels permutation32 permutation7
    mixedMoment B raw39050step0 raw39050step0Labels = mixedMoment B raw39050step1 raw39050step1Labels := by
      have ha : raw39050step1 = -raw39050step0 := by apply Matrix.ext; change ∀ i j, raw39050step1 i j = -(raw39050step0 i j); unfold raw39050step1 raw39050step0; decide +kernel
      have hl : raw39050step1Labels = raw39050step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39050step1 raw39050step1Labels = mixedMoment B raw39050step2 raw39050step2Labels := by
      have ha : raw39050step2 = raw39050step1 := by apply Matrix.ext; unfold raw39050step2 raw39050step1; decide +kernel
      have hl : raw39050step1Labels = labelEmbedding4 ∘ raw39050step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39050step1 raw39050step1Labels raw39050step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3353 node3353Labels := by rfl

def raw39051 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw39051Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw39051step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39051 raw39051Labels = mixedMoment B node2388 node2388Labels := by
  calc
    mixedMoment B raw39051 raw39051Labels = mixedMoment B raw39051step0 raw39051step0Labels := by
      have ha : raw39051step0 = raw39051 := by apply Matrix.ext; unfold raw39051step0 raw39051; decide +kernel
      have hl : raw39051Labels = labelEmbedding2 ∘ raw39051step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39051 raw39051Labels raw39051step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2388 node2388Labels := by rfl

def raw39052 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw39052Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw39052step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw39052step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw39052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39052 raw39052Labels = mixedMoment B node3354 node3354Labels := by
  calc
    mixedMoment B raw39052 raw39052Labels = mixedMoment B raw39052step0 raw39052step0Labels := by
      have ha : raw39052step0 = (fun i j => raw39052 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39052step0 raw39052; decide +kernel
      have hl : raw39052step0Labels = raw39052Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39052 raw39052Labels permutation32 permutation7
    mixedMoment B raw39052step0 raw39052step0Labels = mixedMoment B raw39052step1 raw39052step1Labels := by
      have ha : raw39052step1 = -raw39052step0 := by apply Matrix.ext; change ∀ i j, raw39052step1 i j = -(raw39052step0 i j); unfold raw39052step1 raw39052step0; decide +kernel
      have hl : raw39052step1Labels = raw39052step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39052step1 raw39052step1Labels = mixedMoment B raw39052step2 raw39052step2Labels := by
      have ha : raw39052step2 = raw39052step1 := by apply Matrix.ext; unfold raw39052step2 raw39052step1; decide +kernel
      have hl : raw39052step1Labels = labelEmbedding4 ∘ raw39052step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39052step1 raw39052step1Labels raw39052step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3354 node3354Labels := by rfl

def raw39053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39053Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39053step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39053 raw39053Labels = mixedMoment B node2398 node2398Labels := by
  calc
    mixedMoment B raw39053 raw39053Labels = mixedMoment B raw39053step0 raw39053step0Labels := by
      have ha : raw39053step0 = raw39053 := by apply Matrix.ext; unfold raw39053step0 raw39053; decide +kernel
      have hl : raw39053Labels = labelEmbedding2 ∘ raw39053step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39053 raw39053Labels raw39053step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2398 node2398Labels := by rfl

def raw39054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39054Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39054step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39054step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39054step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39054step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39054step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39054 raw39054Labels = mixedMoment B node3341 node3341Labels := by
  calc
    mixedMoment B raw39054 raw39054Labels = mixedMoment B raw39054step0 raw39054step0Labels := by
      have ha : raw39054step0 = (fun i j => raw39054 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39054step0 raw39054; decide +kernel
      have hl : raw39054step0Labels = raw39054Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39054 raw39054Labels permutation152 permutation7
    mixedMoment B raw39054step0 raw39054step0Labels = mixedMoment B raw39054step1 raw39054step1Labels := by
      have ha : raw39054step1 = -raw39054step0 := by apply Matrix.ext; change ∀ i j, raw39054step1 i j = -(raw39054step0 i j); unfold raw39054step1 raw39054step0; decide +kernel
      have hl : raw39054step1Labels = raw39054step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39054step1 raw39054step1Labels = mixedMoment B raw39054step2 raw39054step2Labels := by
      have ha : raw39054step2 = raw39054step1 := by apply Matrix.ext; unfold raw39054step2 raw39054step1; decide +kernel
      have hl : raw39054step1Labels = labelEmbedding4 ∘ raw39054step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39054step1 raw39054step1Labels raw39054step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3341 node3341Labels := by rfl

def raw39055 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw39055Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw39055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39055 raw39055Labels = mixedMoment B node2399 node2399Labels := by
  calc
    mixedMoment B raw39055 raw39055Labels = mixedMoment B raw39055step0 raw39055step0Labels := by
      have ha : raw39055step0 = raw39055 := by apply Matrix.ext; unfold raw39055step0 raw39055; decide +kernel
      have hl : raw39055Labels = labelEmbedding2 ∘ raw39055step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39055 raw39055Labels raw39055step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2399 node2399Labels := by rfl

def raw39056 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw39056Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw39056step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw39056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39056 raw39056Labels = mixedMoment B node2467 node2467Labels := by
  calc
    mixedMoment B raw39056 raw39056Labels = mixedMoment B raw39056step0 raw39056step0Labels := by
      have ha : raw39056step0 = (fun i j => raw39056 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39056step0 raw39056; decide +kernel
      have hl : raw39056step0Labels = raw39056Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39056 raw39056Labels permutation151 permutation7
    mixedMoment B raw39056step0 raw39056step0Labels = mixedMoment B raw39056step1 raw39056step1Labels := by
      have ha : raw39056step1 = raw39056step0 := by apply Matrix.ext; unfold raw39056step1 raw39056step0; decide +kernel
      have hl : raw39056step0Labels = labelEmbedding4 ∘ raw39056step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39056step0 raw39056step0Labels raw39056step1Labels labelEmbedding4 hl
    _ = mixedMoment B node2467 node2467Labels := by rfl

def raw39057 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw39057Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw39057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39057 raw39057Labels = mixedMoment B node2400 node2400Labels := by
  calc
    mixedMoment B raw39057 raw39057Labels = mixedMoment B raw39057step0 raw39057step0Labels := by
      have ha : raw39057step0 = raw39057 := by apply Matrix.ext; unfold raw39057step0 raw39057; decide +kernel
      have hl : raw39057Labels = labelEmbedding2 ∘ raw39057step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39057 raw39057Labels raw39057step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2400 node2400Labels := by rfl

def raw39058 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw39058Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw39058step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw39058step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39058step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw39058step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39058 raw39058Labels = mixedMoment B node3344 node3344Labels := by
  calc
    mixedMoment B raw39058 raw39058Labels = mixedMoment B raw39058step0 raw39058step0Labels := by
      have ha : raw39058step0 = (fun i j => raw39058 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39058step0 raw39058; decide +kernel
      have hl : raw39058step0Labels = raw39058Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39058 raw39058Labels permutation32 permutation7
    mixedMoment B raw39058step0 raw39058step0Labels = mixedMoment B raw39058step1 raw39058step1Labels := by
      have ha : raw39058step1 = -raw39058step0 := by apply Matrix.ext; change ∀ i j, raw39058step1 i j = -(raw39058step0 i j); unfold raw39058step1 raw39058step0; decide +kernel
      have hl : raw39058step1Labels = raw39058step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39058step1 raw39058step1Labels = mixedMoment B raw39058step2 raw39058step2Labels := by
      have ha : raw39058step2 = raw39058step1 := by apply Matrix.ext; unfold raw39058step2 raw39058step1; decide +kernel
      have hl : raw39058step1Labels = labelEmbedding4 ∘ raw39058step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39058step1 raw39058step1Labels raw39058step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3344 node3344Labels := by rfl

def raw39059 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39059Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39059step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39059 raw39059Labels = mixedMoment B node2404 node2404Labels := by
  calc
    mixedMoment B raw39059 raw39059Labels = mixedMoment B raw39059step0 raw39059step0Labels := by
      have ha : raw39059step0 = raw39059 := by apply Matrix.ext; unfold raw39059step0 raw39059; decide +kernel
      have hl : raw39059Labels = labelEmbedding2 ∘ raw39059step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39059 raw39059Labels raw39059step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2404 node2404Labels := by rfl

def raw39060 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39060Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw39060step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39060step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39060step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39060 raw39060Labels = mixedMoment B node3357 node3357Labels := by
  calc
    mixedMoment B raw39060 raw39060Labels = mixedMoment B raw39060step0 raw39060step0Labels := by
      have ha : raw39060step0 = (fun i j => raw39060 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39060step0 raw39060; decide +kernel
      have hl : raw39060step0Labels = raw39060Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39060 raw39060Labels permutation33 permutation7
    mixedMoment B raw39060step0 raw39060step0Labels = mixedMoment B raw39060step1 raw39060step1Labels := by
      have ha : raw39060step1 = -raw39060step0 := by apply Matrix.ext; change ∀ i j, raw39060step1 i j = -(raw39060step0 i j); unfold raw39060step1 raw39060step0; decide +kernel
      have hl : raw39060step1Labels = raw39060step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39060step1 raw39060step1Labels = mixedMoment B raw39060step2 raw39060step2Labels := by
      have ha : raw39060step2 = raw39060step1 := by apply Matrix.ext; unfold raw39060step2 raw39060step1; decide +kernel
      have hl : raw39060step1Labels = labelEmbedding4 ∘ raw39060step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39060step1 raw39060step1Labels raw39060step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3357 node3357Labels := by rfl

def raw39061 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw39061Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39061step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw39061step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39061 raw39061Labels = mixedMoment B node2407 node2407Labels := by
  calc
    mixedMoment B raw39061 raw39061Labels = mixedMoment B raw39061step0 raw39061step0Labels := by
      have ha : raw39061step0 = raw39061 := by apply Matrix.ext; unfold raw39061step0 raw39061; decide +kernel
      have hl : raw39061Labels = labelEmbedding2 ∘ raw39061step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39061 raw39061Labels raw39061step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2407 node2407Labels := by rfl

def raw39062 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw39062Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39062step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw39062step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39062step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw39062step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39062 raw39062Labels = mixedMoment B node3360 node3360Labels := by
  calc
    mixedMoment B raw39062 raw39062Labels = mixedMoment B raw39062step0 raw39062step0Labels := by
      have ha : raw39062step0 = (fun i j => raw39062 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39062step0 raw39062; decide +kernel
      have hl : raw39062step0Labels = raw39062Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39062 raw39062Labels permutation31 permutation7
    mixedMoment B raw39062step0 raw39062step0Labels = mixedMoment B raw39062step1 raw39062step1Labels := by
      have ha : raw39062step1 = raw39062step0 := by apply Matrix.ext; unfold raw39062step1 raw39062step0; decide +kernel
      have hl : raw39062step0Labels = labelEmbedding4 ∘ raw39062step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39062step0 raw39062step0Labels raw39062step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3360 node3360Labels := by rfl

def raw39063 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw39063Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39063step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw39063step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39063 raw39063Labels = mixedMoment B node2410 node2410Labels := by
  calc
    mixedMoment B raw39063 raw39063Labels = mixedMoment B raw39063step0 raw39063step0Labels := by
      have ha : raw39063step0 = raw39063 := by apply Matrix.ext; unfold raw39063step0 raw39063; decide +kernel
      have hl : raw39063Labels = labelEmbedding2 ∘ raw39063step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39063 raw39063Labels raw39063step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2410 node2410Labels := by rfl

def raw39064 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw39064Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39064step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw39064step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -1, -1], ![2, 1, -3]]
def raw39064step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39064 raw39064Labels = mixedMoment B node2410 node2410Labels := by
  calc
    mixedMoment B raw39064 raw39064Labels = mixedMoment B raw39064step0 raw39064step0Labels := by
      have ha : raw39064step0 = (fun i j => raw39064 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39064step0 raw39064; decide +kernel
      have hl : raw39064step0Labels = raw39064Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39064 raw39064Labels permutation31 permutation7
    mixedMoment B raw39064step0 raw39064step0Labels = mixedMoment B raw39064step1 raw39064step1Labels := by
      have ha : raw39064step1 = raw39064step0 := by apply Matrix.ext; unfold raw39064step1 raw39064step0; decide +kernel
      have hl : raw39064step0Labels = labelEmbedding4 ∘ raw39064step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39064step0 raw39064step0Labels raw39064step1Labels labelEmbedding4 hl
    _ = mixedMoment B node2410 node2410Labels := by rfl

def raw39065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw39065Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw39065step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39065 raw39065Labels = mixedMoment B node2416 node2416Labels := by
  calc
    mixedMoment B raw39065 raw39065Labels = mixedMoment B raw39065step0 raw39065step0Labels := by
      have ha : raw39065step0 = raw39065 := by apply Matrix.ext; unfold raw39065step0 raw39065; decide +kernel
      have hl : raw39065Labels = labelEmbedding2 ∘ raw39065step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39065 raw39065Labels raw39065step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2416 node2416Labels := by rfl

def raw39066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw39066Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw39066step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39066step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw39066step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39066step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 2, -3], ![2, -1, -1]]
def raw39066step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39066 raw39066Labels = mixedMoment B node3427 node3427Labels := by
  calc
    mixedMoment B raw39066 raw39066Labels = mixedMoment B raw39066step0 raw39066step0Labels := by
      have ha : raw39066step0 = (fun i j => raw39066 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39066step0 raw39066; decide +kernel
      have hl : raw39066step0Labels = raw39066Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39066 raw39066Labels permutation153 permutation7
    mixedMoment B raw39066step0 raw39066step0Labels = mixedMoment B raw39066step1 raw39066step1Labels := by
      have ha : raw39066step1 = -raw39066step0 := by apply Matrix.ext; change ∀ i j, raw39066step1 i j = -(raw39066step0 i j); unfold raw39066step1 raw39066step0; decide +kernel
      have hl : raw39066step1Labels = raw39066step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39066step1 raw39066step1Labels = mixedMoment B raw39066step2 raw39066step2Labels := by
      have ha : raw39066step2 = raw39066step1 := by apply Matrix.ext; unfold raw39066step2 raw39066step1; decide +kernel
      have hl : raw39066step1Labels = labelEmbedding4 ∘ raw39066step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39066step1 raw39066step1Labels raw39066step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3427 node3427Labels := by rfl

def raw39067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw39067Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw39067step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39067 raw39067Labels = mixedMoment B node2417 node2417Labels := by
  calc
    mixedMoment B raw39067 raw39067Labels = mixedMoment B raw39067step0 raw39067step0Labels := by
      have ha : raw39067step0 = raw39067 := by apply Matrix.ext; unfold raw39067step0 raw39067; decide +kernel
      have hl : raw39067Labels = labelEmbedding2 ∘ raw39067step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39067 raw39067Labels raw39067step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2417 node2417Labels := by rfl

def raw39068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw39068Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw39068step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw39068step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39068 raw39068Labels = mixedMoment B node2445 node2445Labels := by
  calc
    mixedMoment B raw39068 raw39068Labels = mixedMoment B raw39068step0 raw39068step0Labels := by
      have ha : raw39068step0 = (fun i j => raw39068 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39068step0 raw39068; decide +kernel
      have hl : raw39068step0Labels = raw39068Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39068 raw39068Labels permutation662 permutation7
    mixedMoment B raw39068step0 raw39068step0Labels = mixedMoment B raw39068step1 raw39068step1Labels := by
      have ha : raw39068step1 = raw39068step0 := by apply Matrix.ext; unfold raw39068step1 raw39068step0; decide +kernel
      have hl : raw39068step0Labels = labelEmbedding4 ∘ raw39068step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39068step0 raw39068step0Labels raw39068step1Labels labelEmbedding4 hl
    _ = mixedMoment B node2445 node2445Labels := by rfl

def raw39069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw39069Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw39069step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39069 raw39069Labels = mixedMoment B node2419 node2419Labels := by
  calc
    mixedMoment B raw39069 raw39069Labels = mixedMoment B raw39069step0 raw39069step0Labels := by
      have ha : raw39069step0 = raw39069 := by apply Matrix.ext; unfold raw39069step0 raw39069; decide +kernel
      have hl : raw39069Labels = labelEmbedding2 ∘ raw39069step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39069 raw39069Labels raw39069step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2419 node2419Labels := by rfl

def raw39070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw39070Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 0, 2]]
def raw39070step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw39070step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39070step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, 0, -2]]
def raw39070step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39070 raw39070Labels = mixedMoment B node3425 node3425Labels := by
  calc
    mixedMoment B raw39070 raw39070Labels = mixedMoment B raw39070step0 raw39070step0Labels := by
      have ha : raw39070step0 = (fun i j => raw39070 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39070step0 raw39070; decide +kernel
      have hl : raw39070step0Labels = raw39070Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39070 raw39070Labels permutation154 permutation7
    mixedMoment B raw39070step0 raw39070step0Labels = mixedMoment B raw39070step1 raw39070step1Labels := by
      have ha : raw39070step1 = -raw39070step0 := by apply Matrix.ext; change ∀ i j, raw39070step1 i j = -(raw39070step0 i j); unfold raw39070step1 raw39070step0; decide +kernel
      have hl : raw39070step1Labels = raw39070step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39070step1 raw39070step1Labels = mixedMoment B raw39070step2 raw39070step2Labels := by
      have ha : raw39070step2 = raw39070step1 := by apply Matrix.ext; unfold raw39070step2 raw39070step1; decide +kernel
      have hl : raw39070step1Labels = labelEmbedding4 ∘ raw39070step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39070step1 raw39070step1Labels raw39070step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3425 node3425Labels := by rfl

def raw39071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw39071Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw39071step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39071 raw39071Labels = mixedMoment B node2420 node2420Labels := by
  calc
    mixedMoment B raw39071 raw39071Labels = mixedMoment B raw39071step0 raw39071step0Labels := by
      have ha : raw39071step0 = raw39071 := by apply Matrix.ext; unfold raw39071step0 raw39071; decide +kernel
      have hl : raw39071Labels = labelEmbedding2 ∘ raw39071step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39071 raw39071Labels raw39071step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2420 node2420Labels := by rfl

def raw39072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw39072Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw39072step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39072step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw39072step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39072step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -1, -1]]
def raw39072step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39072 raw39072Labels = mixedMoment B node3428 node3428Labels := by
  calc
    mixedMoment B raw39072 raw39072Labels = mixedMoment B raw39072step0 raw39072step0Labels := by
      have ha : raw39072step0 = (fun i j => raw39072 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39072step0 raw39072; decide +kernel
      have hl : raw39072step0Labels = raw39072Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39072 raw39072Labels permutation155 permutation7
    mixedMoment B raw39072step0 raw39072step0Labels = mixedMoment B raw39072step1 raw39072step1Labels := by
      have ha : raw39072step1 = -raw39072step0 := by apply Matrix.ext; change ∀ i j, raw39072step1 i j = -(raw39072step0 i j); unfold raw39072step1 raw39072step0; decide +kernel
      have hl : raw39072step1Labels = raw39072step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39072step1 raw39072step1Labels = mixedMoment B raw39072step2 raw39072step2Labels := by
      have ha : raw39072step2 = raw39072step1 := by apply Matrix.ext; unfold raw39072step2 raw39072step1; decide +kernel
      have hl : raw39072step1Labels = labelEmbedding4 ∘ raw39072step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39072step1 raw39072step1Labels raw39072step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3428 node3428Labels := by rfl

def raw39073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw39073Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw39073step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39073 raw39073Labels = mixedMoment B node2424 node2424Labels := by
  calc
    mixedMoment B raw39073 raw39073Labels = mixedMoment B raw39073step0 raw39073step0Labels := by
      have ha : raw39073step0 = raw39073 := by apply Matrix.ext; unfold raw39073step0 raw39073; decide +kernel
      have hl : raw39073Labels = labelEmbedding2 ∘ raw39073step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39073 raw39073Labels raw39073step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2424 node2424Labels := by rfl

def raw39074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw39074Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw39074step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39074step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw39074step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39074step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw39074step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39074 raw39074Labels = mixedMoment B node3440 node3440Labels := by
  calc
    mixedMoment B raw39074 raw39074Labels = mixedMoment B raw39074step0 raw39074step0Labels := by
      have ha : raw39074step0 = (fun i j => raw39074 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39074step0 raw39074; decide +kernel
      have hl : raw39074step0Labels = raw39074Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39074 raw39074Labels permutation158 permutation7
    mixedMoment B raw39074step0 raw39074step0Labels = mixedMoment B raw39074step1 raw39074step1Labels := by
      have ha : raw39074step1 = -raw39074step0 := by apply Matrix.ext; change ∀ i j, raw39074step1 i j = -(raw39074step0 i j); unfold raw39074step1 raw39074step0; decide +kernel
      have hl : raw39074step1Labels = raw39074step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39074step1 raw39074step1Labels = mixedMoment B raw39074step2 raw39074step2Labels := by
      have ha : raw39074step2 = raw39074step1 := by apply Matrix.ext; unfold raw39074step2 raw39074step1; decide +kernel
      have hl : raw39074step1Labels = labelEmbedding4 ∘ raw39074step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39074step1 raw39074step1Labels raw39074step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3440 node3440Labels := by rfl

def raw39075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw39075Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw39075step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39075 raw39075Labels = mixedMoment B node2425 node2425Labels := by
  calc
    mixedMoment B raw39075 raw39075Labels = mixedMoment B raw39075step0 raw39075step0Labels := by
      have ha : raw39075step0 = raw39075 := by apply Matrix.ext; unfold raw39075step0 raw39075; decide +kernel
      have hl : raw39075Labels = labelEmbedding2 ∘ raw39075step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39075 raw39075Labels raw39075step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2425 node2425Labels := by rfl

def raw39076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw39076Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw39076step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw39076step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39076 raw39076Labels = mixedMoment B node3449 node3449Labels := by
  calc
    mixedMoment B raw39076 raw39076Labels = mixedMoment B raw39076step0 raw39076step0Labels := by
      have ha : raw39076step0 = (fun i j => raw39076 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39076step0 raw39076; decide +kernel
      have hl : raw39076step0Labels = raw39076Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39076 raw39076Labels permutation688 permutation7
    mixedMoment B raw39076step0 raw39076step0Labels = mixedMoment B raw39076step1 raw39076step1Labels := by
      have ha : raw39076step1 = raw39076step0 := by apply Matrix.ext; unfold raw39076step1 raw39076step0; decide +kernel
      have hl : raw39076step0Labels = labelEmbedding4 ∘ raw39076step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39076step0 raw39076step0Labels raw39076step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3449 node3449Labels := by rfl

def raw39077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw39077Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw39077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39077 raw39077Labels = mixedMoment B node2428 node2428Labels := by
  calc
    mixedMoment B raw39077 raw39077Labels = mixedMoment B raw39077step0 raw39077step0Labels := by
      have ha : raw39077step0 = raw39077 := by apply Matrix.ext; unfold raw39077step0 raw39077; decide +kernel
      have hl : raw39077Labels = labelEmbedding2 ∘ raw39077step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39077 raw39077Labels raw39077step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2428 node2428Labels := by rfl

def raw39078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw39078Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw39078step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39078step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw39078step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39078step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw39078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39078 raw39078Labels = mixedMoment B node3450 node3450Labels := by
  calc
    mixedMoment B raw39078 raw39078Labels = mixedMoment B raw39078step0 raw39078step0Labels := by
      have ha : raw39078step0 = (fun i j => raw39078 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39078step0 raw39078; decide +kernel
      have hl : raw39078step0Labels = raw39078Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39078 raw39078Labels permutation152 permutation7
    mixedMoment B raw39078step0 raw39078step0Labels = mixedMoment B raw39078step1 raw39078step1Labels := by
      have ha : raw39078step1 = -raw39078step0 := by apply Matrix.ext; change ∀ i j, raw39078step1 i j = -(raw39078step0 i j); unfold raw39078step1 raw39078step0; decide +kernel
      have hl : raw39078step1Labels = raw39078step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39078step1 raw39078step1Labels = mixedMoment B raw39078step2 raw39078step2Labels := by
      have ha : raw39078step2 = raw39078step1 := by apply Matrix.ext; unfold raw39078step2 raw39078step1; decide +kernel
      have hl : raw39078step1Labels = labelEmbedding4 ∘ raw39078step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39078step1 raw39078step1Labels raw39078step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3450 node3450Labels := by rfl

def raw39079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39079Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39079step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39079 raw39079Labels = mixedMoment B node2429 node2429Labels := by
  calc
    mixedMoment B raw39079 raw39079Labels = mixedMoment B raw39079step0 raw39079step0Labels := by
      have ha : raw39079step0 = raw39079 := by apply Matrix.ext; unfold raw39079step0 raw39079; decide +kernel
      have hl : raw39079Labels = labelEmbedding2 ∘ raw39079step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39079 raw39079Labels raw39079step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2429 node2429Labels := by rfl

def raw39080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39080Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw39080step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39080step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw39080step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39080step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw39080step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39080 raw39080Labels = mixedMoment B node3455 node3455Labels := by
  calc
    mixedMoment B raw39080 raw39080Labels = mixedMoment B raw39080step0 raw39080step0Labels := by
      have ha : raw39080step0 = (fun i j => raw39080 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39080step0 raw39080; decide +kernel
      have hl : raw39080step0Labels = raw39080Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39080 raw39080Labels permutation152 permutation7
    mixedMoment B raw39080step0 raw39080step0Labels = mixedMoment B raw39080step1 raw39080step1Labels := by
      have ha : raw39080step1 = -raw39080step0 := by apply Matrix.ext; change ∀ i j, raw39080step1 i j = -(raw39080step0 i j); unfold raw39080step1 raw39080step0; decide +kernel
      have hl : raw39080step1Labels = raw39080step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39080step1 raw39080step1Labels = mixedMoment B raw39080step2 raw39080step2Labels := by
      have ha : raw39080step2 = raw39080step1 := by apply Matrix.ext; unfold raw39080step2 raw39080step1; decide +kernel
      have hl : raw39080step1Labels = labelEmbedding4 ∘ raw39080step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39080step1 raw39080step1Labels raw39080step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3455 node3455Labels := by rfl

def raw39081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39081Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39081 raw39081Labels = mixedMoment B node2431 node2431Labels := by
  calc
    mixedMoment B raw39081 raw39081Labels = mixedMoment B raw39081step0 raw39081step0Labels := by
      have ha : raw39081step0 = raw39081 := by apply Matrix.ext; unfold raw39081step0 raw39081; decide +kernel
      have hl : raw39081Labels = labelEmbedding2 ∘ raw39081step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39081 raw39081Labels raw39081step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2431 node2431Labels := by rfl

def raw39082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39082Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw39082step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39082step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw39082step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39082step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw39082step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39082 raw39082Labels = mixedMoment B node3453 node3453Labels := by
  calc
    mixedMoment B raw39082 raw39082Labels = mixedMoment B raw39082step0 raw39082step0Labels := by
      have ha : raw39082step0 = (fun i j => raw39082 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39082step0 raw39082; decide +kernel
      have hl : raw39082step0Labels = raw39082Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39082 raw39082Labels permutation154 permutation7
    mixedMoment B raw39082step0 raw39082step0Labels = mixedMoment B raw39082step1 raw39082step1Labels := by
      have ha : raw39082step1 = -raw39082step0 := by apply Matrix.ext; change ∀ i j, raw39082step1 i j = -(raw39082step0 i j); unfold raw39082step1 raw39082step0; decide +kernel
      have hl : raw39082step1Labels = raw39082step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39082step1 raw39082step1Labels = mixedMoment B raw39082step2 raw39082step2Labels := by
      have ha : raw39082step2 = raw39082step1 := by apply Matrix.ext; unfold raw39082step2 raw39082step1; decide +kernel
      have hl : raw39082step1Labels = labelEmbedding4 ∘ raw39082step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39082step1 raw39082step1Labels raw39082step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3453 node3453Labels := by rfl

def raw39083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39083Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39083step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39083step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39083 raw39083Labels = mixedMoment B node2432 node2432Labels := by
  calc
    mixedMoment B raw39083 raw39083Labels = mixedMoment B raw39083step0 raw39083step0Labels := by
      have ha : raw39083step0 = raw39083 := by apply Matrix.ext; unfold raw39083step0 raw39083; decide +kernel
      have hl : raw39083Labels = labelEmbedding2 ∘ raw39083step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39083 raw39083Labels raw39083step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2432 node2432Labels := by rfl

def raw39084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39084Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw39084step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39084step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw39084step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39084step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw39084step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39084 raw39084Labels = mixedMoment B node3456 node3456Labels := by
  calc
    mixedMoment B raw39084 raw39084Labels = mixedMoment B raw39084step0 raw39084step0Labels := by
      have ha : raw39084step0 = (fun i j => raw39084 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39084step0 raw39084; decide +kernel
      have hl : raw39084step0Labels = raw39084Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39084 raw39084Labels permutation152 permutation7
    mixedMoment B raw39084step0 raw39084step0Labels = mixedMoment B raw39084step1 raw39084step1Labels := by
      have ha : raw39084step1 = -raw39084step0 := by apply Matrix.ext; change ∀ i j, raw39084step1 i j = -(raw39084step0 i j); unfold raw39084step1 raw39084step0; decide +kernel
      have hl : raw39084step1Labels = raw39084step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39084step1 raw39084step1Labels = mixedMoment B raw39084step2 raw39084step2Labels := by
      have ha : raw39084step2 = raw39084step1 := by apply Matrix.ext; unfold raw39084step2 raw39084step1; decide +kernel
      have hl : raw39084step1Labels = labelEmbedding4 ∘ raw39084step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39084step1 raw39084step1Labels raw39084step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3456 node3456Labels := by rfl

def raw39085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw39085Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw39085step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39085 raw39085Labels = mixedMoment B node2444 node2444Labels := by
  calc
    mixedMoment B raw39085 raw39085Labels = mixedMoment B raw39085step0 raw39085step0Labels := by
      have ha : raw39085step0 = raw39085 := by apply Matrix.ext; unfold raw39085step0 raw39085; decide +kernel
      have hl : raw39085Labels = labelEmbedding2 ∘ raw39085step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39085 raw39085Labels raw39085step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2444 node2444Labels := by rfl

def raw39086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw39086Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![1, 0, -1], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw39086step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw39086step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39086step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw39086step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39086 raw39086Labels = mixedMoment B node3362 node3362Labels := by
  calc
    mixedMoment B raw39086 raw39086Labels = mixedMoment B raw39086step0 raw39086step0Labels := by
      have ha : raw39086step0 = (fun i j => raw39086 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39086step0 raw39086; decide +kernel
      have hl : raw39086step0Labels = raw39086Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39086 raw39086Labels permutation176 permutation7
    mixedMoment B raw39086step0 raw39086step0Labels = mixedMoment B raw39086step1 raw39086step1Labels := by
      have ha : raw39086step1 = -raw39086step0 := by apply Matrix.ext; change ∀ i j, raw39086step1 i j = -(raw39086step0 i j); unfold raw39086step1 raw39086step0; decide +kernel
      have hl : raw39086step1Labels = raw39086step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39086step1 raw39086step1Labels = mixedMoment B raw39086step2 raw39086step2Labels := by
      have ha : raw39086step2 = raw39086step1 := by apply Matrix.ext; unfold raw39086step2 raw39086step1; decide +kernel
      have hl : raw39086step1Labels = labelEmbedding4 ∘ raw39086step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39086step1 raw39086step1Labels raw39086step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3362 node3362Labels := by rfl

def raw39087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw39087Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw39087step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39087 raw39087Labels = mixedMoment B node2446 node2446Labels := by
  calc
    mixedMoment B raw39087 raw39087Labels = mixedMoment B raw39087step0 raw39087step0Labels := by
      have ha : raw39087step0 = raw39087 := by apply Matrix.ext; unfold raw39087step0 raw39087; decide +kernel
      have hl : raw39087Labels = labelEmbedding2 ∘ raw39087step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39087 raw39087Labels raw39087step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2446 node2446Labels := by rfl

def raw39088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw39088Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39088step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw39088step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39088step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw39088step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39088step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw39088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39088 raw39088Labels = mixedMoment B node3363 node3363Labels := by
  calc
    mixedMoment B raw39088 raw39088Labels = mixedMoment B raw39088step0 raw39088step0Labels := by
      have ha : raw39088step0 = (fun i j => raw39088 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39088step0 raw39088; decide +kernel
      have hl : raw39088step0Labels = raw39088Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39088 raw39088Labels permutation176 permutation7
    mixedMoment B raw39088step0 raw39088step0Labels = mixedMoment B raw39088step1 raw39088step1Labels := by
      have ha : raw39088step1 = -raw39088step0 := by apply Matrix.ext; change ∀ i j, raw39088step1 i j = -(raw39088step0 i j); unfold raw39088step1 raw39088step0; decide +kernel
      have hl : raw39088step1Labels = raw39088step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39088step1 raw39088step1Labels = mixedMoment B raw39088step2 raw39088step2Labels := by
      have ha : raw39088step2 = raw39088step1 := by apply Matrix.ext; unfold raw39088step2 raw39088step1; decide +kernel
      have hl : raw39088step1Labels = labelEmbedding4 ∘ raw39088step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39088step1 raw39088step1Labels raw39088step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3363 node3363Labels := by rfl

def raw39089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw39089Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw39089step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39089 raw39089Labels = mixedMoment B node2449 node2449Labels := by
  calc
    mixedMoment B raw39089 raw39089Labels = mixedMoment B raw39089step0 raw39089step0Labels := by
      have ha : raw39089step0 = raw39089 := by apply Matrix.ext; unfold raw39089step0 raw39089; decide +kernel
      have hl : raw39089Labels = labelEmbedding2 ∘ raw39089step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39089 raw39089Labels raw39089step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2449 node2449Labels := by rfl

def raw39090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw39090Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw39090step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw39090step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39090 raw39090Labels = mixedMoment B node3432 node3432Labels := by
  calc
    mixedMoment B raw39090 raw39090Labels = mixedMoment B raw39090step0 raw39090step0Labels := by
      have ha : raw39090step0 = (fun i j => raw39090 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39090step0 raw39090; decide +kernel
      have hl : raw39090step0Labels = raw39090Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39090 raw39090Labels permutation688 permutation7
    mixedMoment B raw39090step0 raw39090step0Labels = mixedMoment B raw39090step1 raw39090step1Labels := by
      have ha : raw39090step1 = raw39090step0 := by apply Matrix.ext; unfold raw39090step1 raw39090step0; decide +kernel
      have hl : raw39090step0Labels = labelEmbedding4 ∘ raw39090step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39090step0 raw39090step0Labels raw39090step1Labels labelEmbedding4 hl
    _ = mixedMoment B node3432 node3432Labels := by rfl

def raw39091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw39091Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw39091step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39091 raw39091Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw39091 raw39091Labels = mixedMoment B raw39091step0 raw39091step0Labels := by
      have ha : raw39091step0 = raw39091 := by apply Matrix.ext; unfold raw39091step0 raw39091; decide +kernel
      have hl : raw39091Labels = labelEmbedding2 ∘ raw39091step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39091 raw39091Labels raw39091step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2452 node2452Labels := by rfl

def raw39092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw39092Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39092step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw39092step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39092step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw39092step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39092step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw39092step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39092 raw39092Labels = mixedMoment B node3433 node3433Labels := by
  calc
    mixedMoment B raw39092 raw39092Labels = mixedMoment B raw39092step0 raw39092step0Labels := by
      have ha : raw39092step0 = (fun i j => raw39092 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39092step0 raw39092; decide +kernel
      have hl : raw39092step0Labels = raw39092Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39092 raw39092Labels permutation152 permutation7
    mixedMoment B raw39092step0 raw39092step0Labels = mixedMoment B raw39092step1 raw39092step1Labels := by
      have ha : raw39092step1 = -raw39092step0 := by apply Matrix.ext; change ∀ i j, raw39092step1 i j = -(raw39092step0 i j); unfold raw39092step1 raw39092step0; decide +kernel
      have hl : raw39092step1Labels = raw39092step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39092step1 raw39092step1Labels = mixedMoment B raw39092step2 raw39092step2Labels := by
      have ha : raw39092step2 = raw39092step1 := by apply Matrix.ext; unfold raw39092step2 raw39092step1; decide +kernel
      have hl : raw39092step1Labels = labelEmbedding4 ∘ raw39092step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39092step1 raw39092step1Labels raw39092step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3433 node3433Labels := by rfl

def raw39093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw39093Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39093step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw39093step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39093 raw39093Labels = mixedMoment B node2458 node2458Labels := by
  calc
    mixedMoment B raw39093 raw39093Labels = mixedMoment B raw39093step0 raw39093step0Labels := by
      have ha : raw39093step0 = raw39093 := by apply Matrix.ext; unfold raw39093step0 raw39093; decide +kernel
      have hl : raw39093Labels = labelEmbedding2 ∘ raw39093step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39093 raw39093Labels raw39093step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2458 node2458Labels := by rfl

def raw39094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw39094Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw39094step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw39094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39094 raw39094Labels = mixedMoment B node2458 node2458Labels := by
  calc
    mixedMoment B raw39094 raw39094Labels = mixedMoment B raw39094step0 raw39094step0Labels := by
      have ha : raw39094step0 = (fun i j => raw39094 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39094step0 raw39094; decide +kernel
      have hl : raw39094step0Labels = raw39094Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39094 raw39094Labels permutation688 permutation7
    mixedMoment B raw39094step0 raw39094step0Labels = mixedMoment B raw39094step1 raw39094step1Labels := by
      have ha : raw39094step1 = raw39094step0 := by apply Matrix.ext; unfold raw39094step1 raw39094step0; decide +kernel
      have hl : raw39094step0Labels = labelEmbedding4 ∘ raw39094step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39094step0 raw39094step0Labels raw39094step1Labels labelEmbedding4 hl
    _ = mixedMoment B node2458 node2458Labels := by rfl

def raw39095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw39095Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw39095step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39095 raw39095Labels = mixedMoment B node2459 node2459Labels := by
  calc
    mixedMoment B raw39095 raw39095Labels = mixedMoment B raw39095step0 raw39095step0Labels := by
      have ha : raw39095step0 = raw39095 := by apply Matrix.ext; unfold raw39095step0 raw39095; decide +kernel
      have hl : raw39095Labels = labelEmbedding2 ∘ raw39095step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39095 raw39095Labels raw39095step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2459 node2459Labels := by rfl

def raw39096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw39096Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw39096step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39096step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw39096step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39096step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw39096step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39096 raw39096Labels = mixedMoment B node3429 node3429Labels := by
  calc
    mixedMoment B raw39096 raw39096Labels = mixedMoment B raw39096step0 raw39096step0Labels := by
      have ha : raw39096step0 = (fun i j => raw39096 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39096step0 raw39096; decide +kernel
      have hl : raw39096step0Labels = raw39096Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39096 raw39096Labels permutation152 permutation7
    mixedMoment B raw39096step0 raw39096step0Labels = mixedMoment B raw39096step1 raw39096step1Labels := by
      have ha : raw39096step1 = -raw39096step0 := by apply Matrix.ext; change ∀ i j, raw39096step1 i j = -(raw39096step0 i j); unfold raw39096step1 raw39096step0; decide +kernel
      have hl : raw39096step1Labels = raw39096step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39096step1 raw39096step1Labels = mixedMoment B raw39096step2 raw39096step2Labels := by
      have ha : raw39096step2 = raw39096step1 := by apply Matrix.ext; unfold raw39096step2 raw39096step1; decide +kernel
      have hl : raw39096step1Labels = labelEmbedding4 ∘ raw39096step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39096step1 raw39096step1Labels raw39096step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3429 node3429Labels := by rfl

def raw39097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39097Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39097 raw39097Labels = mixedMoment B node2462 node2462Labels := by
  calc
    mixedMoment B raw39097 raw39097Labels = mixedMoment B raw39097step0 raw39097step0Labels := by
      have ha : raw39097step0 = raw39097 := by apply Matrix.ext; unfold raw39097step0 raw39097; decide +kernel
      have hl : raw39097Labels = labelEmbedding2 ∘ raw39097step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39097 raw39097Labels raw39097step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2462 node2462Labels := by rfl

def raw39098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39098Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw39098step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39098step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39098step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39098step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39098step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39098 raw39098Labels = mixedMoment B node3436 node3436Labels := by
  calc
    mixedMoment B raw39098 raw39098Labels = mixedMoment B raw39098step0 raw39098step0Labels := by
      have ha : raw39098step0 = (fun i j => raw39098 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39098step0 raw39098; decide +kernel
      have hl : raw39098step0Labels = raw39098Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39098 raw39098Labels permutation153 permutation7
    mixedMoment B raw39098step0 raw39098step0Labels = mixedMoment B raw39098step1 raw39098step1Labels := by
      have ha : raw39098step1 = -raw39098step0 := by apply Matrix.ext; change ∀ i j, raw39098step1 i j = -(raw39098step0 i j); unfold raw39098step1 raw39098step0; decide +kernel
      have hl : raw39098step1Labels = raw39098step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39098step1 raw39098step1Labels = mixedMoment B raw39098step2 raw39098step2Labels := by
      have ha : raw39098step2 = raw39098step1 := by apply Matrix.ext; unfold raw39098step2 raw39098step1; decide +kernel
      have hl : raw39098step1Labels = labelEmbedding4 ∘ raw39098step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39098step1 raw39098step1Labels raw39098step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3436 node3436Labels := by rfl

def raw39099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39099Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39099step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39099 raw39099Labels = mixedMoment B node2477 node2477Labels := by
  calc
    mixedMoment B raw39099 raw39099Labels = mixedMoment B raw39099step0 raw39099step0Labels := by
      have ha : raw39099step0 = raw39099 := by apply Matrix.ext; unfold raw39099step0 raw39099; decide +kernel
      have hl : raw39099Labels = labelEmbedding2 ∘ raw39099step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39099 raw39099Labels raw39099step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2477 node2477Labels := by rfl

def raw39100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39100Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw39100step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39100step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39100step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39100step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39100step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39100 raw39100Labels = mixedMoment B node3444 node3444Labels := by
  calc
    mixedMoment B raw39100 raw39100Labels = mixedMoment B raw39100step0 raw39100step0Labels := by
      have ha : raw39100step0 = (fun i j => raw39100 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39100step0 raw39100; decide +kernel
      have hl : raw39100step0Labels = raw39100Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39100 raw39100Labels permutation158 permutation7
    mixedMoment B raw39100step0 raw39100step0Labels = mixedMoment B raw39100step1 raw39100step1Labels := by
      have ha : raw39100step1 = -raw39100step0 := by apply Matrix.ext; change ∀ i j, raw39100step1 i j = -(raw39100step0 i j); unfold raw39100step1 raw39100step0; decide +kernel
      have hl : raw39100step1Labels = raw39100step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39100step1 raw39100step1Labels = mixedMoment B raw39100step2 raw39100step2Labels := by
      have ha : raw39100step2 = raw39100step1 := by apply Matrix.ext; unfold raw39100step2 raw39100step1; decide +kernel
      have hl : raw39100step1Labels = labelEmbedding4 ∘ raw39100step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39100step1 raw39100step1Labels raw39100step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3444 node3444Labels := by rfl

def raw39101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39101Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39101 raw39101Labels = mixedMoment B node2479 node2479Labels := by
  calc
    mixedMoment B raw39101 raw39101Labels = mixedMoment B raw39101step0 raw39101step0Labels := by
      have ha : raw39101step0 = raw39101 := by apply Matrix.ext; unfold raw39101step0 raw39101; decide +kernel
      have hl : raw39101Labels = labelEmbedding2 ∘ raw39101step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39101 raw39101Labels raw39101step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2479 node2479Labels := by rfl

def raw39102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39102Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw39102step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39102step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39102step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39102step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw39102step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39102 raw39102Labels = mixedMoment B node3459 node3459Labels := by
  calc
    mixedMoment B raw39102 raw39102Labels = mixedMoment B raw39102step0 raw39102step0Labels := by
      have ha : raw39102step0 = (fun i j => raw39102 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39102step0 raw39102; decide +kernel
      have hl : raw39102step0Labels = raw39102Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39102 raw39102Labels permutation160 permutation7
    mixedMoment B raw39102step0 raw39102step0Labels = mixedMoment B raw39102step1 raw39102step1Labels := by
      have ha : raw39102step1 = -raw39102step0 := by apply Matrix.ext; change ∀ i j, raw39102step1 i j = -(raw39102step0 i j); unfold raw39102step1 raw39102step0; decide +kernel
      have hl : raw39102step1Labels = raw39102step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39102step1 raw39102step1Labels = mixedMoment B raw39102step2 raw39102step2Labels := by
      have ha : raw39102step2 = raw39102step1 := by apply Matrix.ext; unfold raw39102step2 raw39102step1; decide +kernel
      have hl : raw39102step1Labels = labelEmbedding4 ∘ raw39102step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39102step1 raw39102step1Labels raw39102step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3459 node3459Labels := by rfl

def raw39103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39103Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39103step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39103step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39103 raw39103Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw39103 raw39103Labels = mixedMoment B raw39103step0 raw39103step0Labels := by
      have ha : raw39103step0 = raw39103 := by apply Matrix.ext; unfold raw39103step0 raw39103; decide +kernel
      have hl : raw39103Labels = labelEmbedding2 ∘ raw39103step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39103 raw39103Labels raw39103step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2480 node2480Labels := by rfl

def raw39104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39104Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw39104step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39104step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39104step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39104 raw39104Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw39104 raw39104Labels = mixedMoment B raw39104step0 raw39104step0Labels := by
      have ha : raw39104step0 = (fun i j => raw39104 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39104step0 raw39104; decide +kernel
      have hl : raw39104step0Labels = raw39104Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39104 raw39104Labels permutation158 permutation7
    mixedMoment B raw39104step0 raw39104step0Labels = mixedMoment B raw39104step1 raw39104step1Labels := by
      have ha : raw39104step1 = -raw39104step0 := by apply Matrix.ext; change ∀ i j, raw39104step1 i j = -(raw39104step0 i j); unfold raw39104step1 raw39104step0; decide +kernel
      have hl : raw39104step1Labels = raw39104step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39104step1 raw39104step1Labels = mixedMoment B raw39104step2 raw39104step2Labels := by
      have ha : raw39104step2 = raw39104step1 := by apply Matrix.ext; unfold raw39104step2 raw39104step1; decide +kernel
      have hl : raw39104step1Labels = labelEmbedding4 ∘ raw39104step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39104step1 raw39104step1Labels raw39104step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

def raw39105 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw39105Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw39105step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39105 raw39105Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw39105 raw39105Labels = mixedMoment B raw39105step0 raw39105step0Labels := by
      have ha : raw39105step0 = raw39105 := by apply Matrix.ext; unfold raw39105step0 raw39105; decide +kernel
      have hl : raw39105Labels = labelEmbedding2 ∘ raw39105step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39105 raw39105Labels raw39105step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2482 node2482Labels := by rfl

def raw39106 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw39106Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw39106step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw39106step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39106step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw39106step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39106 raw39106Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw39106 raw39106Labels = mixedMoment B raw39106step0 raw39106step0Labels := by
      have ha : raw39106step0 = (fun i j => raw39106 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39106step0 raw39106; decide +kernel
      have hl : raw39106step0Labels = raw39106Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39106 raw39106Labels permutation34 permutation7
    mixedMoment B raw39106step0 raw39106step0Labels = mixedMoment B raw39106step1 raw39106step1Labels := by
      have ha : raw39106step1 = -raw39106step0 := by apply Matrix.ext; change ∀ i j, raw39106step1 i j = -(raw39106step0 i j); unfold raw39106step1 raw39106step0; decide +kernel
      have hl : raw39106step1Labels = raw39106step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39106step1 raw39106step1Labels = mixedMoment B raw39106step2 raw39106step2Labels := by
      have ha : raw39106step2 = raw39106step1 := by apply Matrix.ext; unfold raw39106step2 raw39106step1; decide +kernel
      have hl : raw39106step1Labels = labelEmbedding4 ∘ raw39106step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39106step1 raw39106step1Labels raw39106step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

def raw39107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39107Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39107 raw39107Labels = mixedMoment B node2483 node2483Labels := by
  calc
    mixedMoment B raw39107 raw39107Labels = mixedMoment B raw39107step0 raw39107step0Labels := by
      have ha : raw39107step0 = raw39107 := by apply Matrix.ext; unfold raw39107step0 raw39107; decide +kernel
      have hl : raw39107Labels = labelEmbedding2 ∘ raw39107step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39107 raw39107Labels raw39107step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2483 node2483Labels := by rfl

def raw39108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw39108Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw39108step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39108step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39108step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39108step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39108step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39108 raw39108Labels = mixedMoment B node3477 node3477Labels := by
  calc
    mixedMoment B raw39108 raw39108Labels = mixedMoment B raw39108step0 raw39108step0Labels := by
      have ha : raw39108step0 = (fun i j => raw39108 (permutation170 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39108step0 raw39108; decide +kernel
      have hl : raw39108step0Labels = raw39108Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39108 raw39108Labels permutation170 permutation7
    mixedMoment B raw39108step0 raw39108step0Labels = mixedMoment B raw39108step1 raw39108step1Labels := by
      have ha : raw39108step1 = -raw39108step0 := by apply Matrix.ext; change ∀ i j, raw39108step1 i j = -(raw39108step0 i j); unfold raw39108step1 raw39108step0; decide +kernel
      have hl : raw39108step1Labels = raw39108step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39108step1 raw39108step1Labels = mixedMoment B raw39108step2 raw39108step2Labels := by
      have ha : raw39108step2 = raw39108step1 := by apply Matrix.ext; unfold raw39108step2 raw39108step1; decide +kernel
      have hl : raw39108step1Labels = labelEmbedding4 ∘ raw39108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39108step1 raw39108step1Labels raw39108step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3477 node3477Labels := by rfl

def raw39109 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39109Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39109step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39109 raw39109Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw39109 raw39109Labels = mixedMoment B raw39109step0 raw39109step0Labels := by
      have ha : raw39109step0 = raw39109 := by apply Matrix.ext; unfold raw39109step0 raw39109; decide +kernel
      have hl : raw39109Labels = labelEmbedding2 ∘ raw39109step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39109 raw39109Labels raw39109step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw39110 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw39110Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw39110step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw39110step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39110step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw39110step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39110 raw39110Labels = mixedMoment B node3481 node3481Labels := by
  calc
    mixedMoment B raw39110 raw39110Labels = mixedMoment B raw39110step0 raw39110step0Labels := by
      have ha : raw39110step0 = (fun i j => raw39110 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39110step0 raw39110; decide +kernel
      have hl : raw39110step0Labels = raw39110Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39110 raw39110Labels permutation32 permutation7
    mixedMoment B raw39110step0 raw39110step0Labels = mixedMoment B raw39110step1 raw39110step1Labels := by
      have ha : raw39110step1 = -raw39110step0 := by apply Matrix.ext; change ∀ i j, raw39110step1 i j = -(raw39110step0 i j); unfold raw39110step1 raw39110step0; decide +kernel
      have hl : raw39110step1Labels = raw39110step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39110step1 raw39110step1Labels = mixedMoment B raw39110step2 raw39110step2Labels := by
      have ha : raw39110step2 = raw39110step1 := by apply Matrix.ext; unfold raw39110step2 raw39110step1; decide +kernel
      have hl : raw39110step1Labels = labelEmbedding4 ∘ raw39110step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39110step1 raw39110step1Labels raw39110step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3481 node3481Labels := by rfl

def raw39111 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39111Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39111step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39111 raw39111Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw39111 raw39111Labels = mixedMoment B raw39111step0 raw39111step0Labels := by
      have ha : raw39111step0 = raw39111 := by apply Matrix.ext; unfold raw39111step0 raw39111; decide +kernel
      have hl : raw39111Labels = labelEmbedding2 ∘ raw39111step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39111 raw39111Labels raw39111step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw39112 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw39112Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw39112step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw39112step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw39112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39112 raw39112Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw39112 raw39112Labels = mixedMoment B raw39112step0 raw39112step0Labels := by
      have ha : raw39112step0 = (fun i j => raw39112 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39112step0 raw39112; decide +kernel
      have hl : raw39112step0Labels = raw39112Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39112 raw39112Labels permutation34 permutation7
    mixedMoment B raw39112step0 raw39112step0Labels = mixedMoment B raw39112step1 raw39112step1Labels := by
      have ha : raw39112step1 = -raw39112step0 := by apply Matrix.ext; change ∀ i j, raw39112step1 i j = -(raw39112step0 i j); unfold raw39112step1 raw39112step0; decide +kernel
      have hl : raw39112step1Labels = raw39112step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39112step1 raw39112step1Labels = mixedMoment B raw39112step2 raw39112step2Labels := by
      have ha : raw39112step2 = raw39112step1 := by apply Matrix.ext; unfold raw39112step2 raw39112step1; decide +kernel
      have hl : raw39112step1Labels = labelEmbedding4 ∘ raw39112step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39112step1 raw39112step1Labels raw39112step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3478 node3478Labels := by rfl

def raw39113 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39113Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39113step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39113 raw39113Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw39113 raw39113Labels = mixedMoment B raw39113step0 raw39113step0Labels := by
      have ha : raw39113step0 = raw39113 := by apply Matrix.ext; unfold raw39113step0 raw39113; decide +kernel
      have hl : raw39113Labels = labelEmbedding2 ∘ raw39113step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39113 raw39113Labels raw39113step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2489 node2489Labels := by rfl

def raw39114 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw39114Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw39114step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw39114step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39114step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw39114step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39114 raw39114Labels = mixedMoment B node3482 node3482Labels := by
  calc
    mixedMoment B raw39114 raw39114Labels = mixedMoment B raw39114step0 raw39114step0Labels := by
      have ha : raw39114step0 = (fun i j => raw39114 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39114step0 raw39114; decide +kernel
      have hl : raw39114step0Labels = raw39114Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39114 raw39114Labels permutation32 permutation7
    mixedMoment B raw39114step0 raw39114step0Labels = mixedMoment B raw39114step1 raw39114step1Labels := by
      have ha : raw39114step1 = -raw39114step0 := by apply Matrix.ext; change ∀ i j, raw39114step1 i j = -(raw39114step0 i j); unfold raw39114step1 raw39114step0; decide +kernel
      have hl : raw39114step1Labels = raw39114step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39114step1 raw39114step1Labels = mixedMoment B raw39114step2 raw39114step2Labels := by
      have ha : raw39114step2 = raw39114step1 := by apply Matrix.ext; unfold raw39114step2 raw39114step1; decide +kernel
      have hl : raw39114step1Labels = labelEmbedding4 ∘ raw39114step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39114step1 raw39114step1Labels raw39114step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3482 node3482Labels := by rfl

def raw39115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39115Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39115step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39115 raw39115Labels = mixedMoment B node2503 node2503Labels := by
  calc
    mixedMoment B raw39115 raw39115Labels = mixedMoment B raw39115step0 raw39115step0Labels := by
      have ha : raw39115step0 = raw39115 := by apply Matrix.ext; unfold raw39115step0 raw39115; decide +kernel
      have hl : raw39115Labels = labelEmbedding2 ∘ raw39115step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39115 raw39115Labels raw39115step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2503 node2503Labels := by rfl

def raw39116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39116Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39116step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39116step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39116step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39116step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39116step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39116step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39116 raw39116Labels = mixedMoment B node3446 node3446Labels := by
  calc
    mixedMoment B raw39116 raw39116Labels = mixedMoment B raw39116step0 raw39116step0Labels := by
      have ha : raw39116step0 = (fun i j => raw39116 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39116step0 raw39116; decide +kernel
      have hl : raw39116step0Labels = raw39116Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39116 raw39116Labels permutation152 permutation7
    mixedMoment B raw39116step0 raw39116step0Labels = mixedMoment B raw39116step1 raw39116step1Labels := by
      have ha : raw39116step1 = -raw39116step0 := by apply Matrix.ext; change ∀ i j, raw39116step1 i j = -(raw39116step0 i j); unfold raw39116step1 raw39116step0; decide +kernel
      have hl : raw39116step1Labels = raw39116step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39116step1 raw39116step1Labels = mixedMoment B raw39116step2 raw39116step2Labels := by
      have ha : raw39116step2 = raw39116step1 := by apply Matrix.ext; unfold raw39116step2 raw39116step1; decide +kernel
      have hl : raw39116step1Labels = labelEmbedding4 ∘ raw39116step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39116step1 raw39116step1Labels raw39116step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3446 node3446Labels := by rfl

def raw39117 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw39117Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw39117step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39117 raw39117Labels = mixedMoment B node2504 node2504Labels := by
  calc
    mixedMoment B raw39117 raw39117Labels = mixedMoment B raw39117step0 raw39117step0Labels := by
      have ha : raw39117step0 = raw39117 := by apply Matrix.ext; unfold raw39117step0 raw39117; decide +kernel
      have hl : raw39117Labels = labelEmbedding2 ∘ raw39117step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39117 raw39117Labels raw39117step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2504 node2504Labels := by rfl

def raw39118 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw39118Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw39118step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw39118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39118 raw39118Labels = mixedMoment B node2504 node2504Labels := by
  calc
    mixedMoment B raw39118 raw39118Labels = mixedMoment B raw39118step0 raw39118step0Labels := by
      have ha : raw39118step0 = (fun i j => raw39118 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39118step0 raw39118; decide +kernel
      have hl : raw39118step0Labels = raw39118Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39118 raw39118Labels permutation151 permutation7
    mixedMoment B raw39118step0 raw39118step0Labels = mixedMoment B raw39118step1 raw39118step1Labels := by
      have ha : raw39118step1 = raw39118step0 := by apply Matrix.ext; unfold raw39118step1 raw39118step0; decide +kernel
      have hl : raw39118step0Labels = labelEmbedding4 ∘ raw39118step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39118step0 raw39118step0Labels raw39118step1Labels labelEmbedding4 hl
    _ = mixedMoment B node2504 node2504Labels := by rfl

def raw39119 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw39119Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw39119step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39119 raw39119Labels = mixedMoment B node2505 node2505Labels := by
  calc
    mixedMoment B raw39119 raw39119Labels = mixedMoment B raw39119step0 raw39119step0Labels := by
      have ha : raw39119step0 = raw39119 := by apply Matrix.ext; unfold raw39119step0 raw39119; decide +kernel
      have hl : raw39119Labels = labelEmbedding2 ∘ raw39119step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39119 raw39119Labels raw39119step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2505 node2505Labels := by rfl

def raw39120 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw39120Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw39120step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw39120step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39120step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw39120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39120 raw39120Labels = mixedMoment B node3448 node3448Labels := by
  calc
    mixedMoment B raw39120 raw39120Labels = mixedMoment B raw39120step0 raw39120step0Labels := by
      have ha : raw39120step0 = (fun i j => raw39120 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39120step0 raw39120; decide +kernel
      have hl : raw39120step0Labels = raw39120Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39120 raw39120Labels permutation32 permutation7
    mixedMoment B raw39120step0 raw39120step0Labels = mixedMoment B raw39120step1 raw39120step1Labels := by
      have ha : raw39120step1 = -raw39120step0 := by apply Matrix.ext; change ∀ i j, raw39120step1 i j = -(raw39120step0 i j); unfold raw39120step1 raw39120step0; decide +kernel
      have hl : raw39120step1Labels = raw39120step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39120step1 raw39120step1Labels = mixedMoment B raw39120step2 raw39120step2Labels := by
      have ha : raw39120step2 = raw39120step1 := by apply Matrix.ext; unfold raw39120step2 raw39120step1; decide +kernel
      have hl : raw39120step1Labels = labelEmbedding4 ∘ raw39120step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39120step1 raw39120step1Labels raw39120step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3448 node3448Labels := by rfl

def raw39121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39121Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39121step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39121 raw39121Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw39121 raw39121Labels = mixedMoment B raw39121step0 raw39121step0Labels := by
      have ha : raw39121step0 = raw39121 := by apply Matrix.ext; unfold raw39121step0 raw39121; decide +kernel
      have hl : raw39121Labels = labelEmbedding2 ∘ raw39121step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39121 raw39121Labels raw39121step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2508 node2508Labels := by rfl

def raw39122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw39122Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw39122step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39122step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39122step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39122step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39122step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39122 raw39122Labels = mixedMoment B node3460 node3460Labels := by
  calc
    mixedMoment B raw39122 raw39122Labels = mixedMoment B raw39122step0 raw39122step0Labels := by
      have ha : raw39122step0 = (fun i j => raw39122 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39122step0 raw39122; decide +kernel
      have hl : raw39122step0Labels = raw39122Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39122 raw39122Labels permutation152 permutation7
    mixedMoment B raw39122step0 raw39122step0Labels = mixedMoment B raw39122step1 raw39122step1Labels := by
      have ha : raw39122step1 = -raw39122step0 := by apply Matrix.ext; change ∀ i j, raw39122step1 i j = -(raw39122step0 i j); unfold raw39122step1 raw39122step0; decide +kernel
      have hl : raw39122step1Labels = raw39122step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39122step1 raw39122step1Labels = mixedMoment B raw39122step2 raw39122step2Labels := by
      have ha : raw39122step2 = raw39122step1 := by apply Matrix.ext; unfold raw39122step2 raw39122step1; decide +kernel
      have hl : raw39122step1Labels = labelEmbedding4 ∘ raw39122step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39122step1 raw39122step1Labels raw39122step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3460 node3460Labels := by rfl

def raw39123 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39123Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39123step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39123 raw39123Labels = mixedMoment B node2509 node2509Labels := by
  calc
    mixedMoment B raw39123 raw39123Labels = mixedMoment B raw39123step0 raw39123step0Labels := by
      have ha : raw39123step0 = raw39123 := by apply Matrix.ext; unfold raw39123step0 raw39123; decide +kernel
      have hl : raw39123Labels = labelEmbedding2 ∘ raw39123step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39123 raw39123Labels raw39123step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2509 node2509Labels := by rfl

def raw39124 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw39124Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw39124step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw39124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39124 raw39124Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw39124 raw39124Labels = mixedMoment B raw39124step0 raw39124step0Labels := by
      have ha : raw39124step0 = (fun i j => raw39124 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39124step0 raw39124; decide +kernel
      have hl : raw39124step0Labels = raw39124Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39124 raw39124Labels permutation145 permutation7
    mixedMoment B raw39124step0 raw39124step0Labels = mixedMoment B raw39124step1 raw39124step1Labels := by
      have ha : raw39124step1 = raw39124step0 := by apply Matrix.ext; unfold raw39124step1 raw39124step0; decide +kernel
      have hl : raw39124step0Labels = labelEmbedding4 ∘ raw39124step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39124step0 raw39124step0Labels raw39124step1Labels labelEmbedding4 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

def raw39125 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw39125Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw39125step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39125 raw39125Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw39125 raw39125Labels = mixedMoment B raw39125step0 raw39125step0Labels := by
      have ha : raw39125step0 = raw39125 := by apply Matrix.ext; unfold raw39125step0 raw39125; decide +kernel
      have hl : raw39125Labels = labelEmbedding2 ∘ raw39125step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39125 raw39125Labels raw39125step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw39126 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw39126Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw39126step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39126step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw39126step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39126 raw39126Labels = mixedMoment B node3471 node3471Labels := by
  calc
    mixedMoment B raw39126 raw39126Labels = mixedMoment B raw39126step0 raw39126step0Labels := by
      have ha : raw39126step0 = (fun i j => raw39126 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39126step0 raw39126; decide +kernel
      have hl : raw39126step0Labels = raw39126Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39126 raw39126Labels permutation33 permutation7
    mixedMoment B raw39126step0 raw39126step0Labels = mixedMoment B raw39126step1 raw39126step1Labels := by
      have ha : raw39126step1 = -raw39126step0 := by apply Matrix.ext; change ∀ i j, raw39126step1 i j = -(raw39126step0 i j); unfold raw39126step1 raw39126step0; decide +kernel
      have hl : raw39126step1Labels = raw39126step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39126step1 raw39126step1Labels = mixedMoment B raw39126step2 raw39126step2Labels := by
      have ha : raw39126step2 = raw39126step1 := by apply Matrix.ext; unfold raw39126step2 raw39126step1; decide +kernel
      have hl : raw39126step1Labels = labelEmbedding4 ∘ raw39126step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39126step1 raw39126step1Labels raw39126step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3471 node3471Labels := by rfl

def raw39127 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39127Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39127step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39127 raw39127Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw39127 raw39127Labels = mixedMoment B raw39127step0 raw39127step0Labels := by
      have ha : raw39127step0 = raw39127 := by apply Matrix.ext; unfold raw39127step0 raw39127; decide +kernel
      have hl : raw39127Labels = labelEmbedding2 ∘ raw39127step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39127 raw39127Labels raw39127step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw39128 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw39128Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw39128step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw39128step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw39128step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39128 raw39128Labels = mixedMoment B node3479 node3479Labels := by
  calc
    mixedMoment B raw39128 raw39128Labels = mixedMoment B raw39128step0 raw39128step0Labels := by
      have ha : raw39128step0 = (fun i j => raw39128 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39128step0 raw39128; decide +kernel
      have hl : raw39128step0Labels = raw39128Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39128 raw39128Labels permutation36 permutation7
    mixedMoment B raw39128step0 raw39128step0Labels = mixedMoment B raw39128step1 raw39128step1Labels := by
      have ha : raw39128step1 = -raw39128step0 := by apply Matrix.ext; change ∀ i j, raw39128step1 i j = -(raw39128step0 i j); unfold raw39128step1 raw39128step0; decide +kernel
      have hl : raw39128step1Labels = raw39128step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39128step1 raw39128step1Labels = mixedMoment B raw39128step2 raw39128step2Labels := by
      have ha : raw39128step2 = raw39128step1 := by apply Matrix.ext; unfold raw39128step2 raw39128step1; decide +kernel
      have hl : raw39128step1Labels = labelEmbedding4 ∘ raw39128step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39128step1 raw39128step1Labels raw39128step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3479 node3479Labels := by rfl

def raw39129 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw39129Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39129step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw39129step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39129 raw39129Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw39129 raw39129Labels = mixedMoment B raw39129step0 raw39129step0Labels := by
      have ha : raw39129step0 = raw39129 := by apply Matrix.ext; unfold raw39129step0 raw39129; decide +kernel
      have hl : raw39129Labels = labelEmbedding2 ∘ raw39129step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39129 raw39129Labels raw39129step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2519 node2519Labels := by rfl

def raw39130 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw39130Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39130step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw39130step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39130step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw39130step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39130step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 2, -3], ![2, -1, -1]]
def raw39130step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39130 raw39130Labels = mixedMoment B node3486 node3486Labels := by
  calc
    mixedMoment B raw39130 raw39130Labels = mixedMoment B raw39130step0 raw39130step0Labels := by
      have ha : raw39130step0 = (fun i j => raw39130 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39130step0 raw39130; decide +kernel
      have hl : raw39130step0Labels = raw39130Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39130 raw39130Labels permutation9 permutation7
    mixedMoment B raw39130step0 raw39130step0Labels = mixedMoment B raw39130step1 raw39130step1Labels := by
      have ha : raw39130step1 = -raw39130step0 := by apply Matrix.ext; change ∀ i j, raw39130step1 i j = -(raw39130step0 i j); unfold raw39130step1 raw39130step0; decide +kernel
      have hl : raw39130step1Labels = raw39130step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39130step1 raw39130step1Labels = mixedMoment B raw39130step2 raw39130step2Labels := by
      have ha : raw39130step2 = raw39130step1 := by apply Matrix.ext; unfold raw39130step2 raw39130step1; decide +kernel
      have hl : raw39130step1Labels = labelEmbedding4 ∘ raw39130step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39130step1 raw39130step1Labels raw39130step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3486 node3486Labels := by rfl

def raw39131 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw39131Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39131step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw39131step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39131 raw39131Labels = mixedMoment B node2522 node2522Labels := by
  calc
    mixedMoment B raw39131 raw39131Labels = mixedMoment B raw39131step0 raw39131step0Labels := by
      have ha : raw39131step0 = raw39131 := by apply Matrix.ext; unfold raw39131step0 raw39131; decide +kernel
      have hl : raw39131Labels = labelEmbedding2 ∘ raw39131step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39131 raw39131Labels raw39131step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2522 node2522Labels := by rfl

def raw39132 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw39132Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39132step0 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw39132step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39132step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw39132step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39132 raw39132Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw39132 raw39132Labels = mixedMoment B raw39132step0 raw39132step0Labels := by
      have ha : raw39132step0 = (fun i j => raw39132 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39132step0 raw39132; decide +kernel
      have hl : raw39132step0Labels = raw39132Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39132 raw39132Labels permutation31 permutation7
    mixedMoment B raw39132step0 raw39132step0Labels = mixedMoment B raw39132step1 raw39132step1Labels := by
      have ha : raw39132step1 = raw39132step0 := by apply Matrix.ext; unfold raw39132step1 raw39132step0; decide +kernel
      have hl : raw39132step0Labels = labelEmbedding4 ∘ raw39132step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39132step0 raw39132step0Labels raw39132step1Labels labelEmbedding4 hl
    _ = mixedMoment B node2685 node2685Labels := by rfl

def raw39133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw39133Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 0, 2]]
def raw39133step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw39133step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39133step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, 0, -2]]
def raw39133step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39133 raw39133Labels = mixedMoment B node3597 node3597Labels := by
  calc
    mixedMoment B raw39133 raw39133Labels = mixedMoment B raw39133step0 raw39133step0Labels := by
      have ha : raw39133step0 = (fun i j => raw39133 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39133step0 raw39133; decide +kernel
      have hl : raw39133step0Labels = raw39133Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39133 raw39133Labels permutation152 permutation7
    mixedMoment B raw39133step0 raw39133step0Labels = mixedMoment B raw39133step1 raw39133step1Labels := by
      have ha : raw39133step1 = -raw39133step0 := by apply Matrix.ext; change ∀ i j, raw39133step1 i j = -(raw39133step0 i j); unfold raw39133step1 raw39133step0; decide +kernel
      have hl : raw39133step1Labels = raw39133step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39133step1 raw39133step1Labels = mixedMoment B raw39133step2 raw39133step2Labels := by
      have ha : raw39133step2 = raw39133step1 := by apply Matrix.ext; unfold raw39133step2 raw39133step1; decide +kernel
      have hl : raw39133step1Labels = labelEmbedding1 ∘ raw39133step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39133step1 raw39133step1Labels raw39133step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3597 node3597Labels := by rfl

def raw39134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39134Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, -1, 2]]
def raw39134step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39134step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw39134step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39134step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 1, -2]]
def raw39134step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39134 raw39134Labels = mixedMoment B node3599 node3599Labels := by
  calc
    mixedMoment B raw39134 raw39134Labels = mixedMoment B raw39134step0 raw39134step0Labels := by
      have ha : raw39134step0 = (fun i j => raw39134 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39134step0 raw39134; decide +kernel
      have hl : raw39134step0Labels = raw39134Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39134 raw39134Labels permutation154 permutation7
    mixedMoment B raw39134step0 raw39134step0Labels = mixedMoment B raw39134step1 raw39134step1Labels := by
      have ha : raw39134step1 = -raw39134step0 := by apply Matrix.ext; change ∀ i j, raw39134step1 i j = -(raw39134step0 i j); unfold raw39134step1 raw39134step0; decide +kernel
      have hl : raw39134step1Labels = raw39134step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39134step1 raw39134step1Labels = mixedMoment B raw39134step2 raw39134step2Labels := by
      have ha : raw39134step2 = raw39134step1 := by apply Matrix.ext; unfold raw39134step2 raw39134step1; decide +kernel
      have hl : raw39134step1Labels = labelEmbedding1 ∘ raw39134step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39134step1 raw39134step1Labels raw39134step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3599 node3599Labels := by rfl

def raw39135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -2, 0]]
def raw39135Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw39135step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39135 raw39135Labels = mixedMoment B node2891 node2891Labels := by
  calc
    mixedMoment B raw39135 raw39135Labels = mixedMoment B raw39135step0 raw39135step0Labels := by
      have ha : raw39135step0 = (fun i j => raw39135 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39135step0 raw39135; decide +kernel
      have hl : raw39135step0Labels = raw39135Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39135 raw39135Labels permutation152 permutation3
    _ = mixedMoment B node2891 node2891Labels := by rfl

def raw39136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -2, 0]]
def raw39136Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![0, -2, 2], ![-2, 1, 1]]
def raw39136step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]
def raw39136step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39136step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![2, -1, -1]]
def raw39136step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39136 raw39136Labels = mixedMoment B node3598 node3598Labels := by
  calc
    mixedMoment B raw39136 raw39136Labels = mixedMoment B raw39136step0 raw39136step0Labels := by
      have ha : raw39136step0 = (fun i j => raw39136 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39136step0 raw39136; decide +kernel
      have hl : raw39136step0Labels = raw39136Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39136 raw39136Labels permutation155 permutation7
    mixedMoment B raw39136step0 raw39136step0Labels = mixedMoment B raw39136step1 raw39136step1Labels := by
      have ha : raw39136step1 = -raw39136step0 := by apply Matrix.ext; change ∀ i j, raw39136step1 i j = -(raw39136step0 i j); unfold raw39136step1 raw39136step0; decide +kernel
      have hl : raw39136step1Labels = raw39136step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39136step1 raw39136step1Labels = mixedMoment B raw39136step2 raw39136step2Labels := by
      have ha : raw39136step2 = raw39136step1 := by apply Matrix.ext; unfold raw39136step2 raw39136step1; decide +kernel
      have hl : raw39136step1Labels = labelEmbedding1 ∘ raw39136step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39136step1 raw39136step1Labels raw39136step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3598 node3598Labels := by rfl

def raw39137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw39137Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, -1, 2]]
def raw39137step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw39137step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39137step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 1, -2]]
def raw39137step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39137 raw39137Labels = mixedMoment B node3604 node3604Labels := by
  calc
    mixedMoment B raw39137 raw39137Labels = mixedMoment B raw39137step0 raw39137step0Labels := by
      have ha : raw39137step0 = (fun i j => raw39137 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39137step0 raw39137; decide +kernel
      have hl : raw39137step0Labels = raw39137Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39137 raw39137Labels permutation160 permutation7
    mixedMoment B raw39137step0 raw39137step0Labels = mixedMoment B raw39137step1 raw39137step1Labels := by
      have ha : raw39137step1 = -raw39137step0 := by apply Matrix.ext; change ∀ i j, raw39137step1 i j = -(raw39137step0 i j); unfold raw39137step1 raw39137step0; decide +kernel
      have hl : raw39137step1Labels = raw39137step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39137step1 raw39137step1Labels = mixedMoment B raw39137step2 raw39137step2Labels := by
      have ha : raw39137step2 = raw39137step1 := by apply Matrix.ext; unfold raw39137step2 raw39137step1; decide +kernel
      have hl : raw39137step1Labels = labelEmbedding1 ∘ raw39137step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39137step1 raw39137step1Labels raw39137step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3604 node3604Labels := by rfl

def raw39138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw39138Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw39138step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39138 raw39138Labels = mixedMoment B node2844 node2844Labels := by
  calc
    mixedMoment B raw39138 raw39138Labels = mixedMoment B raw39138step0 raw39138step0Labels := by
      have ha : raw39138step0 = (fun i j => raw39138 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39138step0 raw39138; decide +kernel
      have hl : raw39138step0Labels = raw39138Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39138 raw39138Labels permutation176 permutation3
    _ = mixedMoment B node2844 node2844Labels := by rfl

def raw39139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw39139Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1]]
def raw39139step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39139step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw39139step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39139step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1]]
def raw39139step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39139 raw39139Labels = mixedMoment B node3609 node3609Labels := by
  calc
    mixedMoment B raw39139 raw39139Labels = mixedMoment B raw39139step0 raw39139step0Labels := by
      have ha : raw39139step0 = (fun i j => raw39139 (permutation168 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39139step0 raw39139; decide +kernel
      have hl : raw39139step0Labels = raw39139Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39139 raw39139Labels permutation168 permutation7
    mixedMoment B raw39139step0 raw39139step0Labels = mixedMoment B raw39139step1 raw39139step1Labels := by
      have ha : raw39139step1 = -raw39139step0 := by apply Matrix.ext; change ∀ i j, raw39139step1 i j = -(raw39139step0 i j); unfold raw39139step1 raw39139step0; decide +kernel
      have hl : raw39139step1Labels = raw39139step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39139step1 raw39139step1Labels = mixedMoment B raw39139step2 raw39139step2Labels := by
      have ha : raw39139step2 = raw39139step1 := by apply Matrix.ext; unfold raw39139step2 raw39139step1; decide +kernel
      have hl : raw39139step1Labels = labelEmbedding1 ∘ raw39139step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39139step1 raw39139step1Labels raw39139step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3609 node3609Labels := by rfl

def raw39140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw39140Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw39140step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39140 raw39140Labels = mixedMoment B node2536 node2536Labels := by
  calc
    mixedMoment B raw39140 raw39140Labels = mixedMoment B raw39140step0 raw39140step0Labels := by
      have ha : raw39140step0 = raw39140 := by apply Matrix.ext; unfold raw39140step0 raw39140; decide +kernel
      have hl : raw39140Labels = labelEmbedding2 ∘ raw39140step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39140 raw39140Labels raw39140step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2536 node2536Labels := by rfl

def raw39141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw39141Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw39141step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw39141step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39141step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw39141step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39141 raw39141Labels = mixedMoment B node3370 node3370Labels := by
  calc
    mixedMoment B raw39141 raw39141Labels = mixedMoment B raw39141step0 raw39141step0Labels := by
      have ha : raw39141step0 = (fun i j => raw39141 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39141step0 raw39141; decide +kernel
      have hl : raw39141step0Labels = raw39141Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39141 raw39141Labels permutation176 permutation7
    mixedMoment B raw39141step0 raw39141step0Labels = mixedMoment B raw39141step1 raw39141step1Labels := by
      have ha : raw39141step1 = -raw39141step0 := by apply Matrix.ext; change ∀ i j, raw39141step1 i j = -(raw39141step0 i j); unfold raw39141step1 raw39141step0; decide +kernel
      have hl : raw39141step1Labels = raw39141step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39141step1 raw39141step1Labels = mixedMoment B raw39141step2 raw39141step2Labels := by
      have ha : raw39141step2 = raw39141step1 := by apply Matrix.ext; unfold raw39141step2 raw39141step1; decide +kernel
      have hl : raw39141step1Labels = labelEmbedding4 ∘ raw39141step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39141step1 raw39141step1Labels raw39141step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3370 node3370Labels := by rfl

def raw39142 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw39142Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw39142step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39142 raw39142Labels = mixedMoment B node2539 node2539Labels := by
  calc
    mixedMoment B raw39142 raw39142Labels = mixedMoment B raw39142step0 raw39142step0Labels := by
      have ha : raw39142step0 = raw39142 := by apply Matrix.ext; unfold raw39142step0 raw39142; decide +kernel
      have hl : raw39142Labels = labelEmbedding2 ∘ raw39142step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39142 raw39142Labels raw39142step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2539 node2539Labels := by rfl

def raw39143 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw39143Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw39143step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw39143step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw39143step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39143 raw39143Labels = mixedMoment B node3372 node3372Labels := by
  calc
    mixedMoment B raw39143 raw39143Labels = mixedMoment B raw39143step0 raw39143step0Labels := by
      have ha : raw39143step0 = (fun i j => raw39143 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39143step0 raw39143; decide +kernel
      have hl : raw39143step0Labels = raw39143Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39143 raw39143Labels permutation38 permutation7
    mixedMoment B raw39143step0 raw39143step0Labels = mixedMoment B raw39143step1 raw39143step1Labels := by
      have ha : raw39143step1 = -raw39143step0 := by apply Matrix.ext; change ∀ i j, raw39143step1 i j = -(raw39143step0 i j); unfold raw39143step1 raw39143step0; decide +kernel
      have hl : raw39143step1Labels = raw39143step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39143step1 raw39143step1Labels = mixedMoment B raw39143step2 raw39143step2Labels := by
      have ha : raw39143step2 = raw39143step1 := by apply Matrix.ext; unfold raw39143step2 raw39143step1; decide +kernel
      have hl : raw39143step1Labels = labelEmbedding4 ∘ raw39143step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39143step1 raw39143step1Labels raw39143step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3372 node3372Labels := by rfl

def raw39144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw39144Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw39144step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39144 raw39144Labels = mixedMoment B node2541 node2541Labels := by
  calc
    mixedMoment B raw39144 raw39144Labels = mixedMoment B raw39144step0 raw39144step0Labels := by
      have ha : raw39144step0 = raw39144 := by apply Matrix.ext; unfold raw39144step0 raw39144; decide +kernel
      have hl : raw39144Labels = labelEmbedding2 ∘ raw39144step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39144 raw39144Labels raw39144step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2541 node2541Labels := by rfl

def raw39145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw39145Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw39145step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39145step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw39145step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39145step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw39145step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39145 raw39145Labels = mixedMoment B node3487 node3487Labels := by
  calc
    mixedMoment B raw39145 raw39145Labels = mixedMoment B raw39145step0 raw39145step0Labels := by
      have ha : raw39145step0 = (fun i j => raw39145 (permutation182 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39145step0 raw39145; decide +kernel
      have hl : raw39145step0Labels = raw39145Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39145 raw39145Labels permutation182 permutation7
    mixedMoment B raw39145step0 raw39145step0Labels = mixedMoment B raw39145step1 raw39145step1Labels := by
      have ha : raw39145step1 = -raw39145step0 := by apply Matrix.ext; change ∀ i j, raw39145step1 i j = -(raw39145step0 i j); unfold raw39145step1 raw39145step0; decide +kernel
      have hl : raw39145step1Labels = raw39145step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39145step1 raw39145step1Labels = mixedMoment B raw39145step2 raw39145step2Labels := by
      have ha : raw39145step2 = raw39145step1 := by apply Matrix.ext; unfold raw39145step2 raw39145step1; decide +kernel
      have hl : raw39145step1Labels = labelEmbedding4 ∘ raw39145step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39145step1 raw39145step1Labels raw39145step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3487 node3487Labels := by rfl

def raw39146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39146Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39146step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39146 raw39146Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw39146 raw39146Labels = mixedMoment B raw39146step0 raw39146step0Labels := by
      have ha : raw39146step0 = raw39146 := by apply Matrix.ext; unfold raw39146step0 raw39146; decide +kernel
      have hl : raw39146Labels = labelEmbedding2 ∘ raw39146step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39146 raw39146Labels raw39146step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2553 node2553Labels := by rfl

def raw39147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw39147Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39147step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw39147step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39147step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw39147step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39147step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw39147step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39147 raw39147Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw39147 raw39147Labels = mixedMoment B raw39147step0 raw39147step0Labels := by
      have ha : raw39147step0 = (fun i j => raw39147 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39147step0 raw39147; decide +kernel
      have hl : raw39147step0Labels = raw39147Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39147 raw39147Labels permutation176 permutation7
    mixedMoment B raw39147step0 raw39147step0Labels = mixedMoment B raw39147step1 raw39147step1Labels := by
      have ha : raw39147step1 = -raw39147step0 := by apply Matrix.ext; change ∀ i j, raw39147step1 i j = -(raw39147step0 i j); unfold raw39147step1 raw39147step0; decide +kernel
      have hl : raw39147step1Labels = raw39147step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39147step1 raw39147step1Labels = mixedMoment B raw39147step2 raw39147step2Labels := by
      have ha : raw39147step2 = raw39147step1 := by apply Matrix.ext; unfold raw39147step2 raw39147step1; decide +kernel
      have hl : raw39147step1Labels = labelEmbedding4 ∘ raw39147step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39147step1 raw39147step1Labels raw39147step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

def raw39148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39148Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39148step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39148step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39148 raw39148Labels = mixedMoment B node2556 node2556Labels := by
  calc
    mixedMoment B raw39148 raw39148Labels = mixedMoment B raw39148step0 raw39148step0Labels := by
      have ha : raw39148step0 = raw39148 := by apply Matrix.ext; unfold raw39148step0 raw39148; decide +kernel
      have hl : raw39148Labels = labelEmbedding2 ∘ raw39148step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39148 raw39148Labels raw39148step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2556 node2556Labels := by rfl

def raw39149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw39149Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw39149step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39149step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39149step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39149step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw39149step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39149 raw39149Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw39149 raw39149Labels = mixedMoment B raw39149step0 raw39149step0Labels := by
      have ha : raw39149step0 = (fun i j => raw39149 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39149step0 raw39149; decide +kernel
      have hl : raw39149step0Labels = raw39149Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39149 raw39149Labels permutation176 permutation7
    mixedMoment B raw39149step0 raw39149step0Labels = mixedMoment B raw39149step1 raw39149step1Labels := by
      have ha : raw39149step1 = -raw39149step0 := by apply Matrix.ext; change ∀ i j, raw39149step1 i j = -(raw39149step0 i j); unfold raw39149step1 raw39149step0; decide +kernel
      have hl : raw39149step1Labels = raw39149step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39149step1 raw39149step1Labels = mixedMoment B raw39149step2 raw39149step2Labels := by
      have ha : raw39149step2 = raw39149step1 := by apply Matrix.ext; unfold raw39149step2 raw39149step1; decide +kernel
      have hl : raw39149step1Labels = labelEmbedding4 ∘ raw39149step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39149step1 raw39149step1Labels raw39149step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

def raw39150 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw39150Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw39150step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39150 raw39150Labels = mixedMoment B node2561 node2561Labels := by
  calc
    mixedMoment B raw39150 raw39150Labels = mixedMoment B raw39150step0 raw39150step0Labels := by
      have ha : raw39150step0 = raw39150 := by apply Matrix.ext; unfold raw39150step0 raw39150; decide +kernel
      have hl : raw39150Labels = labelEmbedding2 ∘ raw39150step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39150 raw39150Labels raw39150step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2561 node2561Labels := by rfl

def raw39151 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw39151Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw39151step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw39151step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39151step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw39151step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39151 raw39151Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw39151 raw39151Labels = mixedMoment B raw39151step0 raw39151step0Labels := by
      have ha : raw39151step0 = (fun i j => raw39151 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39151step0 raw39151; decide +kernel
      have hl : raw39151step0Labels = raw39151Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39151 raw39151Labels permutation38 permutation7
    mixedMoment B raw39151step0 raw39151step0Labels = mixedMoment B raw39151step1 raw39151step1Labels := by
      have ha : raw39151step1 = -raw39151step0 := by apply Matrix.ext; change ∀ i j, raw39151step1 i j = -(raw39151step0 i j); unfold raw39151step1 raw39151step0; decide +kernel
      have hl : raw39151step1Labels = raw39151step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39151step1 raw39151step1Labels = mixedMoment B raw39151step2 raw39151step2Labels := by
      have ha : raw39151step2 = raw39151step1 := by apply Matrix.ext; unfold raw39151step2 raw39151step1; decide +kernel
      have hl : raw39151step1Labels = labelEmbedding4 ∘ raw39151step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39151step1 raw39151step1Labels raw39151step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

def raw39152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw39152Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39152step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0]]
def raw39152step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39152step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39152step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39152step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw39152step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39152 raw39152Labels = mixedMoment B node3610 node3610Labels := by
  calc
    mixedMoment B raw39152 raw39152Labels = mixedMoment B raw39152step0 raw39152step0Labels := by
      have ha : raw39152step0 = (fun i j => raw39152 (permutation168 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39152step0 raw39152; decide +kernel
      have hl : raw39152step0Labels = raw39152Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39152 raw39152Labels permutation168 permutation7
    mixedMoment B raw39152step0 raw39152step0Labels = mixedMoment B raw39152step1 raw39152step1Labels := by
      have ha : raw39152step1 = -raw39152step0 := by apply Matrix.ext; change ∀ i j, raw39152step1 i j = -(raw39152step0 i j); unfold raw39152step1 raw39152step0; decide +kernel
      have hl : raw39152step1Labels = raw39152step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39152step1 raw39152step1Labels = mixedMoment B raw39152step2 raw39152step2Labels := by
      have ha : raw39152step2 = raw39152step1 := by apply Matrix.ext; unfold raw39152step2 raw39152step1; decide +kernel
      have hl : raw39152step1Labels = labelEmbedding1 ∘ raw39152step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39152step1 raw39152step1Labels raw39152step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3610 node3610Labels := by rfl

def raw39153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw39153Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw39153step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39153step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw39153step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39153step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw39153step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39153 raw39153Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw39153 raw39153Labels = mixedMoment B raw39153step0 raw39153step0Labels := by
      have ha : raw39153step0 = (fun i j => raw39153 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39153step0 raw39153; decide +kernel
      have hl : raw39153step0Labels = raw39153Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39153 raw39153Labels permutation162 permutation7
    mixedMoment B raw39153step0 raw39153step0Labels = mixedMoment B raw39153step1 raw39153step1Labels := by
      have ha : raw39153step1 = -raw39153step0 := by apply Matrix.ext; change ∀ i j, raw39153step1 i j = -(raw39153step0 i j); unfold raw39153step1 raw39153step0; decide +kernel
      have hl : raw39153step1Labels = raw39153step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39153step1 raw39153step1Labels = mixedMoment B raw39153step2 raw39153step2Labels := by
      have ha : raw39153step2 = raw39153step1 := by apply Matrix.ext; unfold raw39153step2 raw39153step1; decide +kernel
      have hl : raw39153step1Labels = labelEmbedding1 ∘ raw39153step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39153step1 raw39153step1Labels raw39153step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

def raw39154 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39154Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw39154step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39154 raw39154Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw39154 raw39154Labels = mixedMoment B raw39154step0 raw39154step0Labels := by
      have ha : raw39154step0 = (fun i j => raw39154 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39154step0 raw39154; decide +kernel
      have hl : raw39154step0Labels = raw39154Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39154 raw39154Labels permutation33 permutation3
    _ = mixedMoment B node2931 node2931Labels := by rfl

def raw39155 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw39155Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2]]
def raw39155step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw39155step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39155step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2]]
def raw39155step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39155 raw39155Labels = mixedMoment B node3612 node3612Labels := by
  calc
    mixedMoment B raw39155 raw39155Labels = mixedMoment B raw39155step0 raw39155step0Labels := by
      have ha : raw39155step0 = (fun i j => raw39155 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39155step0 raw39155; decide +kernel
      have hl : raw39155step0Labels = raw39155Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39155 raw39155Labels permutation34 permutation7
    mixedMoment B raw39155step0 raw39155step0Labels = mixedMoment B raw39155step1 raw39155step1Labels := by
      have ha : raw39155step1 = -raw39155step0 := by apply Matrix.ext; change ∀ i j, raw39155step1 i j = -(raw39155step0 i j); unfold raw39155step1 raw39155step0; decide +kernel
      have hl : raw39155step1Labels = raw39155step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39155step1 raw39155step1Labels = mixedMoment B raw39155step2 raw39155step2Labels := by
      have ha : raw39155step2 = raw39155step1 := by apply Matrix.ext; unfold raw39155step2 raw39155step1; decide +kernel
      have hl : raw39155step1Labels = labelEmbedding1 ∘ raw39155step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39155step1 raw39155step1Labels raw39155step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3612 node3612Labels := by rfl

def raw39156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw39156Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39156step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw39156step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39156step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw39156step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39156step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw39156step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39156 raw39156Labels = mixedMoment B node3600 node3600Labels := by
  calc
    mixedMoment B raw39156 raw39156Labels = mixedMoment B raw39156step0 raw39156step0Labels := by
      have ha : raw39156step0 = (fun i j => raw39156 (permutation161 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39156step0 raw39156; decide +kernel
      have hl : raw39156step0Labels = raw39156Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39156 raw39156Labels permutation161 permutation7
    mixedMoment B raw39156step0 raw39156step0Labels = mixedMoment B raw39156step1 raw39156step1Labels := by
      have ha : raw39156step1 = -raw39156step0 := by apply Matrix.ext; change ∀ i j, raw39156step1 i j = -(raw39156step0 i j); unfold raw39156step1 raw39156step0; decide +kernel
      have hl : raw39156step1Labels = raw39156step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39156step1 raw39156step1Labels = mixedMoment B raw39156step2 raw39156step2Labels := by
      have ha : raw39156step2 = raw39156step1 := by apply Matrix.ext; unfold raw39156step2 raw39156step1; decide +kernel
      have hl : raw39156step1Labels = labelEmbedding1 ∘ raw39156step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39156step1 raw39156step1Labels raw39156step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3600 node3600Labels := by rfl

def raw39157 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw39157Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw39157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw39157step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39157 raw39157Labels = mixedMoment B node2911 node2911Labels := by
  calc
    mixedMoment B raw39157 raw39157Labels = mixedMoment B raw39157step0 raw39157step0Labels := by
      have ha : raw39157step0 = (fun i j => raw39157 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw39157step0 raw39157; decide +kernel
      have hl : raw39157step0Labels = raw39157Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39157 raw39157Labels permutation32 permutation3
    _ = mixedMoment B node2911 node2911Labels := by rfl

def raw39158 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw39158Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw39158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![0, -2, 2], ![-2, 2, 0]]
def raw39158step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]
def raw39158step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw39158step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![2, -2, 0]]
def raw39158step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39158 raw39158Labels = mixedMoment B node3611 node3611Labels := by
  calc
    mixedMoment B raw39158 raw39158Labels = mixedMoment B raw39158step0 raw39158step0Labels := by
      have ha : raw39158step0 = (fun i j => raw39158 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39158step0 raw39158; decide +kernel
      have hl : raw39158step0Labels = raw39158Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39158 raw39158Labels permutation35 permutation7
    mixedMoment B raw39158step0 raw39158step0Labels = mixedMoment B raw39158step1 raw39158step1Labels := by
      have ha : raw39158step1 = -raw39158step0 := by apply Matrix.ext; change ∀ i j, raw39158step1 i j = -(raw39158step0 i j); unfold raw39158step1 raw39158step0; decide +kernel
      have hl : raw39158step1Labels = raw39158step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39158step1 raw39158step1Labels = mixedMoment B raw39158step2 raw39158step2Labels := by
      have ha : raw39158step2 = raw39158step1 := by apply Matrix.ext; unfold raw39158step2 raw39158step1; decide +kernel
      have hl : raw39158step1Labels = labelEmbedding1 ∘ raw39158step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39158step1 raw39158step1Labels raw39158step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3611 node3611Labels := by rfl

def raw39159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39159Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39159step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39159 raw39159Labels = mixedMoment B node2589 node2589Labels := by
  calc
    mixedMoment B raw39159 raw39159Labels = mixedMoment B raw39159step0 raw39159step0Labels := by
      have ha : raw39159step0 = raw39159 := by apply Matrix.ext; unfold raw39159step0 raw39159; decide +kernel
      have hl : raw39159Labels = labelEmbedding2 ∘ raw39159step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39159 raw39159Labels raw39159step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2589 node2589Labels := by rfl

def raw39160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39160Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw39160step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39160step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39160step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39160step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39160step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39160 raw39160Labels = mixedMoment B node3563 node3563Labels := by
  calc
    mixedMoment B raw39160 raw39160Labels = mixedMoment B raw39160step0 raw39160step0Labels := by
      have ha : raw39160step0 = (fun i j => raw39160 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39160step0 raw39160; decide +kernel
      have hl : raw39160step0Labels = raw39160Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39160 raw39160Labels permutation176 permutation7
    mixedMoment B raw39160step0 raw39160step0Labels = mixedMoment B raw39160step1 raw39160step1Labels := by
      have ha : raw39160step1 = -raw39160step0 := by apply Matrix.ext; change ∀ i j, raw39160step1 i j = -(raw39160step0 i j); unfold raw39160step1 raw39160step0; decide +kernel
      have hl : raw39160step1Labels = raw39160step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39160step1 raw39160step1Labels = mixedMoment B raw39160step2 raw39160step2Labels := by
      have ha : raw39160step2 = raw39160step1 := by apply Matrix.ext; unfold raw39160step2 raw39160step1; decide +kernel
      have hl : raw39160step1Labels = labelEmbedding4 ∘ raw39160step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39160step1 raw39160step1Labels raw39160step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3563 node3563Labels := by rfl

def raw39161 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39161Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39161step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39161 raw39161Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw39161 raw39161Labels = mixedMoment B raw39161step0 raw39161step0Labels := by
      have ha : raw39161step0 = raw39161 := by apply Matrix.ext; unfold raw39161step0 raw39161; decide +kernel
      have hl : raw39161Labels = labelEmbedding2 ∘ raw39161step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39161 raw39161Labels raw39161step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2590 node2590Labels := by rfl

def raw39162 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39162Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw39162step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39162step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw39162step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39162 raw39162Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw39162 raw39162Labels = mixedMoment B raw39162step0 raw39162step0Labels := by
      have ha : raw39162step0 = (fun i j => raw39162 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39162step0 raw39162; decide +kernel
      have hl : raw39162step0Labels = raw39162Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39162 raw39162Labels permutation38 permutation7
    mixedMoment B raw39162step0 raw39162step0Labels = mixedMoment B raw39162step1 raw39162step1Labels := by
      have ha : raw39162step1 = -raw39162step0 := by apply Matrix.ext; change ∀ i j, raw39162step1 i j = -(raw39162step0 i j); unfold raw39162step1 raw39162step0; decide +kernel
      have hl : raw39162step1Labels = raw39162step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39162step1 raw39162step1Labels = mixedMoment B raw39162step2 raw39162step2Labels := by
      have ha : raw39162step2 = raw39162step1 := by apply Matrix.ext; unfold raw39162step2 raw39162step1; decide +kernel
      have hl : raw39162step1Labels = labelEmbedding4 ∘ raw39162step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39162step1 raw39162step1Labels raw39162step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

def raw39163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39163Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39163step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39163 raw39163Labels = mixedMoment B node2593 node2593Labels := by
  calc
    mixedMoment B raw39163 raw39163Labels = mixedMoment B raw39163step0 raw39163step0Labels := by
      have ha : raw39163step0 = raw39163 := by apply Matrix.ext; unfold raw39163step0 raw39163; decide +kernel
      have hl : raw39163Labels = labelEmbedding2 ∘ raw39163step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39163 raw39163Labels raw39163step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2593 node2593Labels := by rfl

def raw39164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw39164Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw39164step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39164step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39164step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39164step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw39164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39164 raw39164Labels = mixedMoment B node3602 node3602Labels := by
  calc
    mixedMoment B raw39164 raw39164Labels = mixedMoment B raw39164step0 raw39164step0Labels := by
      have ha : raw39164step0 = (fun i j => raw39164 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39164step0 raw39164; decide +kernel
      have hl : raw39164step0Labels = raw39164Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39164 raw39164Labels permutation152 permutation7
    mixedMoment B raw39164step0 raw39164step0Labels = mixedMoment B raw39164step1 raw39164step1Labels := by
      have ha : raw39164step1 = -raw39164step0 := by apply Matrix.ext; change ∀ i j, raw39164step1 i j = -(raw39164step0 i j); unfold raw39164step1 raw39164step0; decide +kernel
      have hl : raw39164step1Labels = raw39164step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39164step1 raw39164step1Labels = mixedMoment B raw39164step2 raw39164step2Labels := by
      have ha : raw39164step2 = raw39164step1 := by apply Matrix.ext; unfold raw39164step2 raw39164step1; decide +kernel
      have hl : raw39164step1Labels = labelEmbedding4 ∘ raw39164step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39164step1 raw39164step1Labels raw39164step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3602 node3602Labels := by rfl

def raw39165 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39165Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39165step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39165 raw39165Labels = mixedMoment B node2594 node2594Labels := by
  calc
    mixedMoment B raw39165 raw39165Labels = mixedMoment B raw39165step0 raw39165step0Labels := by
      have ha : raw39165step0 = raw39165 := by apply Matrix.ext; unfold raw39165step0 raw39165; decide +kernel
      have hl : raw39165Labels = labelEmbedding2 ∘ raw39165step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39165 raw39165Labels raw39165step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2594 node2594Labels := by rfl

def raw39166 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw39166Labels : Fin 3 → Fin 3 := ![0, 2, 2]

def raw39166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw39166step0Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39166step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw39166step1Labels : Fin 3 → Fin 3 := ![2, 2, 0]

def raw39166step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw39166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39166 raw39166Labels = mixedMoment B node3603 node3603Labels := by
  calc
    mixedMoment B raw39166 raw39166Labels = mixedMoment B raw39166step0 raw39166step0Labels := by
      have ha : raw39166step0 = (fun i j => raw39166 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw39166step0 raw39166; decide +kernel
      have hl : raw39166step0Labels = raw39166Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw39166 raw39166Labels permutation32 permutation7
    mixedMoment B raw39166step0 raw39166step0Labels = mixedMoment B raw39166step1 raw39166step1Labels := by
      have ha : raw39166step1 = -raw39166step0 := by apply Matrix.ext; change ∀ i j, raw39166step1 i j = -(raw39166step0 i j); unfold raw39166step1 raw39166step0; decide +kernel
      have hl : raw39166step1Labels = raw39166step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw39166step1 raw39166step1Labels = mixedMoment B raw39166step2 raw39166step2Labels := by
      have ha : raw39166step2 = raw39166step1 := by apply Matrix.ext; unfold raw39166step2 raw39166step1; decide +kernel
      have hl : raw39166step1Labels = labelEmbedding4 ∘ raw39166step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39166step1 raw39166step1Labels raw39166step2Labels labelEmbedding4 hl
    _ = mixedMoment B node3603 node3603Labels := by rfl

def raw39167 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39167Labels : Fin 3 → Fin 3 := ![0, 0, 2]

def raw39167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw39167step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical39167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw39167 raw39167Labels = mixedMoment B node2595 node2595Labels := by
  calc
    mixedMoment B raw39167 raw39167Labels = mixedMoment B raw39167step0 raw39167step0Labels := by
      have ha : raw39167step0 = raw39167 := by apply Matrix.ext; unfold raw39167step0 raw39167; decide +kernel
      have hl : raw39167Labels = labelEmbedding2 ∘ raw39167step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw39167 raw39167Labels raw39167step0Labels labelEmbedding2 hl
    _ = mixedMoment B node2595 node2595Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
