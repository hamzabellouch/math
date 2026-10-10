import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw23040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23040step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23040step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23040step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23040 raw23040Labels = mixedMoment B node4313 node4313Labels := by
  calc
    mixedMoment B raw23040 raw23040Labels = mixedMoment B raw23040step0 raw23040step0Labels := by
      have hz : ∀ j, raw23040 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23040step0 = (fun i j => raw23040 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23040step0 raw23040; decide +kernel
      have hl : raw23040step0Labels = raw23040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23040 raw23040Labels permutation346 hz
    mixedMoment B raw23040step0 raw23040step0Labels = mixedMoment B raw23040step1 raw23040step1Labels := by
      have ha : raw23040step1 = (fun i j => raw23040step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23040step1 raw23040step0; decide +kernel
      have hl : raw23040step1Labels = raw23040step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23040step0 raw23040step0Labels permutation39 permutation3
    mixedMoment B raw23040step1 raw23040step1Labels = mixedMoment B raw23040step2 raw23040step2Labels := by
      have ha : raw23040step2 = raw23040step1 := by apply Matrix.ext; unfold raw23040step2 raw23040step1; decide +kernel
      have hl : raw23040step1Labels = labelEmbedding6 ∘ raw23040step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23040step1 raw23040step1Labels raw23040step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4313 node4313Labels := by rfl

def raw23041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23041step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23041step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw23041step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23041step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23041step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23041step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23041step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23041 raw23041Labels = mixedMoment B node4491 node4491Labels := by
  calc
    mixedMoment B raw23041 raw23041Labels = mixedMoment B raw23041step0 raw23041step0Labels := by
      have hz : ∀ j, raw23041 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23041step0 = (fun i j => raw23041 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23041step0 raw23041; decide +kernel
      have hl : raw23041step0Labels = raw23041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23041 raw23041Labels permutation434 hz
    mixedMoment B raw23041step0 raw23041step0Labels = mixedMoment B raw23041step1 raw23041step1Labels := by
      have hz : ∀ j, raw23041step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23041step1 = (fun i j => raw23041step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23041step1 raw23041step0; decide +kernel
      have hl : raw23041step1Labels = raw23041step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23041step0 raw23041step0Labels permutation80 hz
    mixedMoment B raw23041step1 raw23041step1Labels = mixedMoment B raw23041step2 raw23041step2Labels := by
      have ha : raw23041step2 = (fun i j => raw23041step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23041step2 raw23041step1; decide +kernel
      have hl : raw23041step2Labels = raw23041step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23041step1 raw23041step1Labels permutation12 permutation3
    mixedMoment B raw23041step2 raw23041step2Labels = mixedMoment B raw23041step3 raw23041step3Labels := by
      have ha : raw23041step3 = raw23041step2 := by apply Matrix.ext; unfold raw23041step3 raw23041step2; decide +kernel
      have hl : raw23041step2Labels = labelEmbedding6 ∘ raw23041step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23041step2 raw23041step2Labels raw23041step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4491 node4491Labels := by rfl

def raw23042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23042step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23042step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23042step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23042step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23042 raw23042Labels = mixedMoment B node4106 node4106Labels := by
  calc
    mixedMoment B raw23042 raw23042Labels = mixedMoment B raw23042step0 raw23042step0Labels := by
      have hz : ∀ j, raw23042 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23042step0 = (fun i j => raw23042 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23042step0 raw23042; decide +kernel
      have hl : raw23042step0Labels = raw23042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23042 raw23042Labels permutation434 hz
    mixedMoment B raw23042step0 raw23042step0Labels = mixedMoment B raw23042step1 raw23042step1Labels := by
      have ha : raw23042step1 = (fun i j => raw23042step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23042step1 raw23042step0; decide +kernel
      have hl : raw23042step1Labels = raw23042step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23042step0 raw23042step0Labels permutation33 permutation3
    mixedMoment B raw23042step1 raw23042step1Labels = mixedMoment B raw23042step2 raw23042step2Labels := by
      have ha : raw23042step2 = raw23042step1 := by apply Matrix.ext; unfold raw23042step2 raw23042step1; decide +kernel
      have hl : raw23042step1Labels = labelEmbedding6 ∘ raw23042step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23042step1 raw23042step1Labels raw23042step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4106 node4106Labels := by rfl

def raw23043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23043step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23043step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23043step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23043 raw23043Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw23043 raw23043Labels = mixedMoment B raw23043step0 raw23043step0Labels := by
      have hz : ∀ j, raw23043 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23043step0 = (fun i j => raw23043 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23043step0 raw23043; decide +kernel
      have hl : raw23043step0Labels = raw23043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23043 raw23043Labels permutation434 hz
    mixedMoment B raw23043step0 raw23043step0Labels = mixedMoment B raw23043step1 raw23043step1Labels := by
      have ha : raw23043step1 = (fun i j => raw23043step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23043step1 raw23043step0; decide +kernel
      have hl : raw23043step1Labels = raw23043step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23043step0 raw23043step0Labels permutation33 permutation3
    mixedMoment B raw23043step1 raw23043step1Labels = mixedMoment B raw23043step2 raw23043step2Labels := by
      have ha : raw23043step2 = raw23043step1 := by apply Matrix.ext; unfold raw23043step2 raw23043step1; decide +kernel
      have hl : raw23043step1Labels = labelEmbedding6 ∘ raw23043step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23043step1 raw23043step1Labels raw23043step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4354 node4354Labels := by rfl

def raw23044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23044step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23044step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23044step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23044 raw23044Labels = mixedMoment B node4291 node4291Labels := by
  calc
    mixedMoment B raw23044 raw23044Labels = mixedMoment B raw23044step0 raw23044step0Labels := by
      have ha : raw23044step0 = (fun i j => raw23044 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23044step0 raw23044; decide +kernel
      have hl : raw23044step0Labels = raw23044Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23044 raw23044Labels permutation201 permutation3
    mixedMoment B raw23044step0 raw23044step0Labels = mixedMoment B raw23044step1 raw23044step1Labels := by
      have ha : raw23044step1 = raw23044step0 := by apply Matrix.ext; unfold raw23044step1 raw23044step0; decide +kernel
      have hl : raw23044step0Labels = labelEmbedding6 ∘ raw23044step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23044step0 raw23044step0Labels raw23044step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4291 node4291Labels := by rfl

def raw23045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23045step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw23045step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23045step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw23045step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23045 raw23045Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw23045 raw23045Labels = mixedMoment B raw23045step0 raw23045step0Labels := by
      have hz : ∀ j, raw23045 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23045step0 = (fun i j => raw23045 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23045step0 raw23045; decide +kernel
      have hl : raw23045step0Labels = raw23045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23045 raw23045Labels permutation434 hz
    mixedMoment B raw23045step0 raw23045step0Labels = mixedMoment B raw23045step1 raw23045step1Labels := by
      have ha : raw23045step1 = (fun i j => raw23045step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23045step1 raw23045step0; decide +kernel
      have hl : raw23045step1Labels = raw23045step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23045step0 raw23045step0Labels permutation36 permutation3
    mixedMoment B raw23045step1 raw23045step1Labels = mixedMoment B raw23045step2 raw23045step2Labels := by
      have ha : raw23045step2 = raw23045step1 := by apply Matrix.ext; unfold raw23045step2 raw23045step1; decide +kernel
      have hl : raw23045step1Labels = labelEmbedding6 ∘ raw23045step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23045step1 raw23045step1Labels raw23045step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

def raw23046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23046step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23046step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23046step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23046step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23046step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23046 raw23046Labels = mixedMoment B node4106 node4106Labels := by
  calc
    mixedMoment B raw23046 raw23046Labels = mixedMoment B raw23046step0 raw23046step0Labels := by
      have hz : ∀ j, raw23046 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23046step0 = (fun i j => raw23046 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23046step0 raw23046; decide +kernel
      have hl : raw23046step0Labels = raw23046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23046 raw23046Labels permutation346 hz
    mixedMoment B raw23046step0 raw23046step0Labels = mixedMoment B raw23046step1 raw23046step1Labels := by
      have ha : raw23046step1 = (fun i j => raw23046step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23046step1 raw23046step0; decide +kernel
      have hl : raw23046step1Labels = raw23046step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23046step0 raw23046step0Labels permutation33 permutation3
    mixedMoment B raw23046step1 raw23046step1Labels = mixedMoment B raw23046step2 raw23046step2Labels := by
      have ha : raw23046step2 = raw23046step1 := by apply Matrix.ext; unfold raw23046step2 raw23046step1; decide +kernel
      have hl : raw23046step1Labels = labelEmbedding6 ∘ raw23046step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23046step1 raw23046step1Labels raw23046step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4106 node4106Labels := by rfl

def raw23047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23047step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23047step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23047step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23047step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23047 raw23047Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw23047 raw23047Labels = mixedMoment B raw23047step0 raw23047step0Labels := by
      have hz : ∀ j, raw23047 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23047step0 = (fun i j => raw23047 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23047step0 raw23047; decide +kernel
      have hl : raw23047step0Labels = raw23047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23047 raw23047Labels permutation346 hz
    mixedMoment B raw23047step0 raw23047step0Labels = mixedMoment B raw23047step1 raw23047step1Labels := by
      have ha : raw23047step1 = (fun i j => raw23047step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23047step1 raw23047step0; decide +kernel
      have hl : raw23047step1Labels = raw23047step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23047step0 raw23047step0Labels permutation33 permutation3
    mixedMoment B raw23047step1 raw23047step1Labels = mixedMoment B raw23047step2 raw23047step2Labels := by
      have ha : raw23047step2 = raw23047step1 := by apply Matrix.ext; unfold raw23047step2 raw23047step1; decide +kernel
      have hl : raw23047step1Labels = labelEmbedding6 ∘ raw23047step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23047step1 raw23047step1Labels raw23047step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4354 node4354Labels := by rfl

def raw23048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23048step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23048step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23048step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23048 raw23048Labels = mixedMoment B node4291 node4291Labels := by
  calc
    mixedMoment B raw23048 raw23048Labels = mixedMoment B raw23048step0 raw23048step0Labels := by
      have ha : raw23048step0 = (fun i j => raw23048 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23048step0 raw23048; decide +kernel
      have hl : raw23048step0Labels = raw23048Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23048 raw23048Labels permutation177 permutation3
    mixedMoment B raw23048step0 raw23048step0Labels = mixedMoment B raw23048step1 raw23048step1Labels := by
      have ha : raw23048step1 = raw23048step0 := by apply Matrix.ext; unfold raw23048step1 raw23048step0; decide +kernel
      have hl : raw23048step0Labels = labelEmbedding6 ∘ raw23048step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23048step0 raw23048step0Labels raw23048step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4291 node4291Labels := by rfl

def raw23049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23049step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23049step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![3, -3, 0], ![2, 0, -2]]
def raw23049step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23049step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23049step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23049step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23049step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23049 raw23049Labels = mixedMoment B node4109 node4109Labels := by
  calc
    mixedMoment B raw23049 raw23049Labels = mixedMoment B raw23049step0 raw23049step0Labels := by
      have hz : ∀ j, raw23049 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23049step0 = (fun i j => raw23049 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23049step0 raw23049; decide +kernel
      have hl : raw23049step0Labels = raw23049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23049 raw23049Labels permutation434 hz
    mixedMoment B raw23049step0 raw23049step0Labels = mixedMoment B raw23049step1 raw23049step1Labels := by
      have hz : ∀ j, raw23049step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23049step1 = (fun i j => raw23049step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23049step1 raw23049step0; decide +kernel
      have hl : raw23049step1Labels = raw23049step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23049step0 raw23049step0Labels permutation80 hz
    mixedMoment B raw23049step1 raw23049step1Labels = mixedMoment B raw23049step2 raw23049step2Labels := by
      have ha : raw23049step2 = (fun i j => raw23049step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23049step2 raw23049step1; decide +kernel
      have hl : raw23049step2Labels = raw23049step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23049step1 raw23049step1Labels permutation9 permutation3
    mixedMoment B raw23049step2 raw23049step2Labels = mixedMoment B raw23049step3 raw23049step3Labels := by
      have ha : raw23049step3 = raw23049step2 := by apply Matrix.ext; unfold raw23049step3 raw23049step2; decide +kernel
      have hl : raw23049step2Labels = labelEmbedding6 ∘ raw23049step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23049step2 raw23049step2Labels raw23049step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4109 node4109Labels := by rfl

def raw23050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23050step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23050step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![3, -3, 0], ![2, 0, -2]]
def raw23050step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23050step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw23050step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23050step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw23050step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23050 raw23050Labels = mixedMoment B node4359 node4359Labels := by
  calc
    mixedMoment B raw23050 raw23050Labels = mixedMoment B raw23050step0 raw23050step0Labels := by
      have hz : ∀ j, raw23050 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23050step0 = (fun i j => raw23050 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23050step0 raw23050; decide +kernel
      have hl : raw23050step0Labels = raw23050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23050 raw23050Labels permutation434 hz
    mixedMoment B raw23050step0 raw23050step0Labels = mixedMoment B raw23050step1 raw23050step1Labels := by
      have hz : ∀ j, raw23050step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23050step1 = (fun i j => raw23050step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23050step1 raw23050step0; decide +kernel
      have hl : raw23050step1Labels = raw23050step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23050step0 raw23050step0Labels permutation80 hz
    mixedMoment B raw23050step1 raw23050step1Labels = mixedMoment B raw23050step2 raw23050step2Labels := by
      have ha : raw23050step2 = (fun i j => raw23050step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23050step2 raw23050step1; decide +kernel
      have hl : raw23050step2Labels = raw23050step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23050step1 raw23050step1Labels permutation9 permutation3
    mixedMoment B raw23050step2 raw23050step2Labels = mixedMoment B raw23050step3 raw23050step3Labels := by
      have ha : raw23050step3 = raw23050step2 := by apply Matrix.ext; unfold raw23050step3 raw23050step2; decide +kernel
      have hl : raw23050step2Labels = labelEmbedding6 ∘ raw23050step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23050step2 raw23050step2Labels raw23050step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4359 node4359Labels := by rfl

def raw23051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23051step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23051step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23051step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23051 raw23051Labels = mixedMoment B node4294 node4294Labels := by
  calc
    mixedMoment B raw23051 raw23051Labels = mixedMoment B raw23051step0 raw23051step0Labels := by
      have hz : ∀ j, raw23051 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23051step0 = (fun i j => raw23051 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23051step0 raw23051; decide +kernel
      have hl : raw23051step0Labels = raw23051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23051 raw23051Labels permutation434 hz
    mixedMoment B raw23051step0 raw23051step0Labels = mixedMoment B raw23051step1 raw23051step1Labels := by
      have ha : raw23051step1 = (fun i j => raw23051step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23051step1 raw23051step0; decide +kernel
      have hl : raw23051step1Labels = raw23051step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23051step0 raw23051step0Labels permutation39 permutation3
    mixedMoment B raw23051step1 raw23051step1Labels = mixedMoment B raw23051step2 raw23051step2Labels := by
      have ha : raw23051step2 = raw23051step1 := by apply Matrix.ext; unfold raw23051step2 raw23051step1; decide +kernel
      have hl : raw23051step1Labels = labelEmbedding6 ∘ raw23051step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23051step1 raw23051step1Labels raw23051step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4294 node4294Labels := by rfl

def raw23052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23052step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23052step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23052step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23052 raw23052Labels = mixedMoment B node4294 node4294Labels := by
  calc
    mixedMoment B raw23052 raw23052Labels = mixedMoment B raw23052step0 raw23052step0Labels := by
      have hz : ∀ j, raw23052 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23052step0 = (fun i j => raw23052 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23052step0 raw23052; decide +kernel
      have hl : raw23052step0Labels = raw23052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23052 raw23052Labels permutation346 hz
    mixedMoment B raw23052step0 raw23052step0Labels = mixedMoment B raw23052step1 raw23052step1Labels := by
      have ha : raw23052step1 = (fun i j => raw23052step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23052step1 raw23052step0; decide +kernel
      have hl : raw23052step1Labels = raw23052step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23052step0 raw23052step0Labels permutation39 permutation3
    mixedMoment B raw23052step1 raw23052step1Labels = mixedMoment B raw23052step2 raw23052step2Labels := by
      have ha : raw23052step2 = raw23052step1 := by apply Matrix.ext; unfold raw23052step2 raw23052step1; decide +kernel
      have hl : raw23052step1Labels = labelEmbedding6 ∘ raw23052step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23052step1 raw23052step1Labels raw23052step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4294 node4294Labels := by rfl

def raw23053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw23053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw23053step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![3, -3, 0], ![1, 1, -2]]
def raw23053step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23053step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw23053step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23053step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw23053step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23053 raw23053Labels = mixedMoment B node4454 node4454Labels := by
  calc
    mixedMoment B raw23053 raw23053Labels = mixedMoment B raw23053step0 raw23053step0Labels := by
      have hz : ∀ j, raw23053 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23053step0 = (fun i j => raw23053 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23053step0 raw23053; decide +kernel
      have hl : raw23053step0Labels = raw23053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23053 raw23053Labels permutation434 hz
    mixedMoment B raw23053step0 raw23053step0Labels = mixedMoment B raw23053step1 raw23053step1Labels := by
      have hz : ∀ j, raw23053step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23053step1 = (fun i j => raw23053step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23053step1 raw23053step0; decide +kernel
      have hl : raw23053step1Labels = raw23053step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23053step0 raw23053step0Labels permutation80 hz
    mixedMoment B raw23053step1 raw23053step1Labels = mixedMoment B raw23053step2 raw23053step2Labels := by
      have ha : raw23053step2 = (fun i j => raw23053step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23053step2 raw23053step1; decide +kernel
      have hl : raw23053step2Labels = raw23053step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23053step1 raw23053step1Labels permutation9 permutation3
    mixedMoment B raw23053step2 raw23053step2Labels = mixedMoment B raw23053step3 raw23053step3Labels := by
      have ha : raw23053step3 = raw23053step2 := by apply Matrix.ext; unfold raw23053step3 raw23053step2; decide +kernel
      have hl : raw23053step2Labels = labelEmbedding6 ∘ raw23053step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23053step2 raw23053step2Labels raw23053step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4454 node4454Labels := by rfl

def raw23054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw23054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw23054step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23054step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw23054step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23054step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23054step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw23054step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23054step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23054 raw23054Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw23054 raw23054Labels = mixedMoment B raw23054step0 raw23054step0Labels := by
      have hz : ∀ j, raw23054 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23054step0 = (fun i j => raw23054 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23054step0 raw23054; decide +kernel
      have hl : raw23054step0Labels = raw23054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23054 raw23054Labels permutation434 hz
    mixedMoment B raw23054step0 raw23054step0Labels = mixedMoment B raw23054step1 raw23054step1Labels := by
      have hz : ∀ j, raw23054step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23054step1 = (fun i j => raw23054step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23054step1 raw23054step0; decide +kernel
      have hl : raw23054step1Labels = raw23054step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23054step0 raw23054step0Labels permutation80 hz
    mixedMoment B raw23054step1 raw23054step1Labels = mixedMoment B raw23054step2 raw23054step2Labels := by
      have ha : raw23054step2 = (fun i j => raw23054step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23054step2 raw23054step1; decide +kernel
      have hl : raw23054step2Labels = raw23054step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23054step1 raw23054step1Labels permutation8 permutation3
    mixedMoment B raw23054step2 raw23054step2Labels = mixedMoment B raw23054step3 raw23054step3Labels := by
      have ha : raw23054step3 = raw23054step2 := by apply Matrix.ext; unfold raw23054step3 raw23054step2; decide +kernel
      have hl : raw23054step2Labels = labelEmbedding6 ∘ raw23054step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23054step2 raw23054step2Labels raw23054step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw23055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23055Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23055step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23055step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23055step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23055step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23055step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23055 raw23055Labels = mixedMoment B node2604 node2604Labels := by
  calc
    mixedMoment B raw23055 raw23055Labels = mixedMoment B raw23055step0 raw23055step0Labels := by
      have hz : ∀ j, raw23055 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23055step0 = (fun i j => raw23055 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23055step0 raw23055; decide +kernel
      have hl : raw23055step0Labels = raw23055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23055 raw23055Labels permutation434 hz
    mixedMoment B raw23055step0 raw23055step0Labels = mixedMoment B raw23055step1 raw23055step1Labels := by
      have hz : ∀ j, raw23055step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23055step1 = (fun i j => raw23055step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23055step1 raw23055step0; decide +kernel
      have hl : raw23055step1Labels = raw23055step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23055step0 raw23055step0Labels permutation80 hz
    mixedMoment B raw23055step1 raw23055step1Labels = mixedMoment B raw23055step2 raw23055step2Labels := by
      have ha : raw23055step2 = (fun i j => raw23055step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23055step2 raw23055step1; decide +kernel
      have hl : raw23055step2Labels = raw23055step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23055step1 raw23055step1Labels permutation9 permutation3
    _ = mixedMoment B node2604 node2604Labels := by rfl

def raw23056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23056Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23056step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23056 raw23056Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw23056 raw23056Labels = mixedMoment B raw23056step0 raw23056step0Labels := by
      have hz : ∀ j, raw23056 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23056step0 = (fun i j => raw23056 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23056step0 raw23056; decide +kernel
      have hl : raw23056step0Labels = raw23056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23056 raw23056Labels permutation434 hz
    mixedMoment B raw23056step0 raw23056step0Labels = mixedMoment B raw23056step1 raw23056step1Labels := by
      have ha : raw23056step1 = (fun i j => raw23056step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23056step1 raw23056step0; decide +kernel
      have hl : raw23056step1Labels = raw23056step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23056step0 raw23056step0Labels permutation39 permutation3
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw23057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23057Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23057step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23057 raw23057Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw23057 raw23057Labels = mixedMoment B raw23057step0 raw23057step0Labels := by
      have hz : ∀ j, raw23057 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23057step0 = (fun i j => raw23057 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23057step0 raw23057; decide +kernel
      have hl : raw23057step0Labels = raw23057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23057 raw23057Labels permutation346 hz
    mixedMoment B raw23057step0 raw23057step0Labels = mixedMoment B raw23057step1 raw23057step1Labels := by
      have ha : raw23057step1 = (fun i j => raw23057step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23057step1 raw23057step0; decide +kernel
      have hl : raw23057step1Labels = raw23057step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23057step0 raw23057step0Labels permutation39 permutation3
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw23058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23058step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23058step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23058step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23058step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23058step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23058 raw23058Labels = mixedMoment B node562 node562Labels := by
  calc
    mixedMoment B raw23058 raw23058Labels = mixedMoment B raw23058step0 raw23058step0Labels := by
      have hz : ∀ j, raw23058 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23058step0 = (fun i j => raw23058 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23058step0 raw23058; decide +kernel
      have hl : raw23058step0Labels = raw23058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23058 raw23058Labels permutation434 hz
    mixedMoment B raw23058step0 raw23058step0Labels = mixedMoment B raw23058step1 raw23058step1Labels := by
      have hz : ∀ j, raw23058step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23058step1 = (fun i j => raw23058step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23058step1 raw23058step0; decide +kernel
      have hl : raw23058step1Labels = raw23058step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23058step0 raw23058step0Labels permutation80 hz
    mixedMoment B raw23058step1 raw23058step1Labels = mixedMoment B raw23058step2 raw23058step2Labels := by
      have ha : raw23058step2 = (fun i j => raw23058step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23058step2 raw23058step1; decide +kernel
      have hl : raw23058step2Labels = raw23058step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23058step1 raw23058step1Labels permutation9 permutation3
    _ = mixedMoment B node562 node562Labels := by rfl

def raw23059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23059Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23059step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23059 raw23059Labels = mixedMoment B node891 node891Labels := by
  calc
    mixedMoment B raw23059 raw23059Labels = mixedMoment B raw23059step0 raw23059step0Labels := by
      have hz : ∀ j, raw23059 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23059step0 = (fun i j => raw23059 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23059step0 raw23059; decide +kernel
      have hl : raw23059step0Labels = raw23059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23059 raw23059Labels permutation434 hz
    mixedMoment B raw23059step0 raw23059step0Labels = mixedMoment B raw23059step1 raw23059step1Labels := by
      have ha : raw23059step1 = (fun i j => raw23059step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23059step1 raw23059step0; decide +kernel
      have hl : raw23059step1Labels = raw23059step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23059step0 raw23059step0Labels permutation39 permutation3
    _ = mixedMoment B node891 node891Labels := by rfl

def raw23060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23060Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23060step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23060step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23060 raw23060Labels = mixedMoment B node891 node891Labels := by
  calc
    mixedMoment B raw23060 raw23060Labels = mixedMoment B raw23060step0 raw23060step0Labels := by
      have hz : ∀ j, raw23060 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23060step0 = (fun i j => raw23060 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23060step0 raw23060; decide +kernel
      have hl : raw23060step0Labels = raw23060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23060 raw23060Labels permutation346 hz
    mixedMoment B raw23060step0 raw23060step0Labels = mixedMoment B raw23060step1 raw23060step1Labels := by
      have ha : raw23060step1 = (fun i j => raw23060step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23060step1 raw23060step0; decide +kernel
      have hl : raw23060step1Labels = raw23060step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23060step0 raw23060step0Labels permutation39 permutation3
    _ = mixedMoment B node891 node891Labels := by rfl

def raw23061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23061Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23061step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23061step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw23061step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23061step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw23061step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23061 raw23061Labels = mixedMoment B node1075 node1075Labels := by
  calc
    mixedMoment B raw23061 raw23061Labels = mixedMoment B raw23061step0 raw23061step0Labels := by
      have hz : ∀ j, raw23061 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23061step0 = (fun i j => raw23061 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23061step0 raw23061; decide +kernel
      have hl : raw23061step0Labels = raw23061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23061 raw23061Labels permutation434 hz
    mixedMoment B raw23061step0 raw23061step0Labels = mixedMoment B raw23061step1 raw23061step1Labels := by
      have hz : ∀ j, raw23061step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23061step1 = (fun i j => raw23061step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23061step1 raw23061step0; decide +kernel
      have hl : raw23061step1Labels = raw23061step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23061step0 raw23061step0Labels permutation80 hz
    mixedMoment B raw23061step1 raw23061step1Labels = mixedMoment B raw23061step2 raw23061step2Labels := by
      have ha : raw23061step2 = (fun i j => raw23061step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23061step2 raw23061step1; decide +kernel
      have hl : raw23061step2Labels = raw23061step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23061step1 raw23061step1Labels permutation12 permutation3
    _ = mixedMoment B node1075 node1075Labels := by rfl

def raw23062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23062Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23062step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23062step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23062 raw23062Labels = mixedMoment B node543 node543Labels := by
  calc
    mixedMoment B raw23062 raw23062Labels = mixedMoment B raw23062step0 raw23062step0Labels := by
      have hz : ∀ j, raw23062 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23062step0 = (fun i j => raw23062 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23062step0 raw23062; decide +kernel
      have hl : raw23062step0Labels = raw23062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23062 raw23062Labels permutation434 hz
    mixedMoment B raw23062step0 raw23062step0Labels = mixedMoment B raw23062step1 raw23062step1Labels := by
      have ha : raw23062step1 = (fun i j => raw23062step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23062step1 raw23062step0; decide +kernel
      have hl : raw23062step1Labels = raw23062step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23062step0 raw23062step0Labels permutation33 permutation3
    _ = mixedMoment B node543 node543Labels := by rfl

def raw23063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23063Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23063step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23063 raw23063Labels = mixedMoment B node932 node932Labels := by
  calc
    mixedMoment B raw23063 raw23063Labels = mixedMoment B raw23063step0 raw23063step0Labels := by
      have hz : ∀ j, raw23063 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23063step0 = (fun i j => raw23063 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23063step0 raw23063; decide +kernel
      have hl : raw23063step0Labels = raw23063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23063 raw23063Labels permutation434 hz
    mixedMoment B raw23063step0 raw23063step0Labels = mixedMoment B raw23063step1 raw23063step1Labels := by
      have ha : raw23063step1 = (fun i j => raw23063step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23063step1 raw23063step0; decide +kernel
      have hl : raw23063step1Labels = raw23063step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23063step0 raw23063step0Labels permutation33 permutation3
    _ = mixedMoment B node932 node932Labels := by rfl

def raw23064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23064Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23064step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23064 raw23064Labels = mixedMoment B node869 node869Labels := by
  calc
    mixedMoment B raw23064 raw23064Labels = mixedMoment B raw23064step0 raw23064step0Labels := by
      have ha : raw23064step0 = (fun i j => raw23064 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23064step0 raw23064; decide +kernel
      have hl : raw23064step0Labels = raw23064Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23064 raw23064Labels permutation201 permutation3
    _ = mixedMoment B node869 node869Labels := by rfl

def raw23065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23065Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw23065step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw23065step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23065 raw23065Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw23065 raw23065Labels = mixedMoment B raw23065step0 raw23065step0Labels := by
      have hz : ∀ j, raw23065 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23065step0 = (fun i j => raw23065 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23065step0 raw23065; decide +kernel
      have hl : raw23065step0Labels = raw23065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23065 raw23065Labels permutation434 hz
    mixedMoment B raw23065step0 raw23065step0Labels = mixedMoment B raw23065step1 raw23065step1Labels := by
      have ha : raw23065step1 = (fun i j => raw23065step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23065step1 raw23065step0; decide +kernel
      have hl : raw23065step1Labels = raw23065step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23065step0 raw23065step0Labels permutation36 permutation3
    _ = mixedMoment B node1035 node1035Labels := by rfl

def raw23066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23066Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23066step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23066step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23066 raw23066Labels = mixedMoment B node543 node543Labels := by
  calc
    mixedMoment B raw23066 raw23066Labels = mixedMoment B raw23066step0 raw23066step0Labels := by
      have hz : ∀ j, raw23066 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23066step0 = (fun i j => raw23066 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23066step0 raw23066; decide +kernel
      have hl : raw23066step0Labels = raw23066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23066 raw23066Labels permutation346 hz
    mixedMoment B raw23066step0 raw23066step0Labels = mixedMoment B raw23066step1 raw23066step1Labels := by
      have ha : raw23066step1 = (fun i j => raw23066step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23066step1 raw23066step0; decide +kernel
      have hl : raw23066step1Labels = raw23066step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23066step0 raw23066step0Labels permutation33 permutation3
    _ = mixedMoment B node543 node543Labels := by rfl

def raw23067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23067Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23067step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23067step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23067step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23067 raw23067Labels = mixedMoment B node932 node932Labels := by
  calc
    mixedMoment B raw23067 raw23067Labels = mixedMoment B raw23067step0 raw23067step0Labels := by
      have hz : ∀ j, raw23067 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23067step0 = (fun i j => raw23067 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23067step0 raw23067; decide +kernel
      have hl : raw23067step0Labels = raw23067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23067 raw23067Labels permutation346 hz
    mixedMoment B raw23067step0 raw23067step0Labels = mixedMoment B raw23067step1 raw23067step1Labels := by
      have ha : raw23067step1 = (fun i j => raw23067step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23067step1 raw23067step0; decide +kernel
      have hl : raw23067step1Labels = raw23067step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23067step0 raw23067step0Labels permutation33 permutation3
    _ = mixedMoment B node932 node932Labels := by rfl

def raw23068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw23068Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23068step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23068 raw23068Labels = mixedMoment B node869 node869Labels := by
  calc
    mixedMoment B raw23068 raw23068Labels = mixedMoment B raw23068step0 raw23068step0Labels := by
      have ha : raw23068step0 = (fun i j => raw23068 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23068step0 raw23068; decide +kernel
      have hl : raw23068step0Labels = raw23068Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23068 raw23068Labels permutation177 permutation3
    _ = mixedMoment B node869 node869Labels := by rfl

def raw23069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23069Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23069step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![3, -3, 0], ![2, 0, -2]]
def raw23069step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23069step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23069step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23069 raw23069Labels = mixedMoment B node546 node546Labels := by
  calc
    mixedMoment B raw23069 raw23069Labels = mixedMoment B raw23069step0 raw23069step0Labels := by
      have hz : ∀ j, raw23069 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23069step0 = (fun i j => raw23069 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23069step0 raw23069; decide +kernel
      have hl : raw23069step0Labels = raw23069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23069 raw23069Labels permutation434 hz
    mixedMoment B raw23069step0 raw23069step0Labels = mixedMoment B raw23069step1 raw23069step1Labels := by
      have hz : ∀ j, raw23069step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23069step1 = (fun i j => raw23069step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23069step1 raw23069step0; decide +kernel
      have hl : raw23069step1Labels = raw23069step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23069step0 raw23069step0Labels permutation80 hz
    mixedMoment B raw23069step1 raw23069step1Labels = mixedMoment B raw23069step2 raw23069step2Labels := by
      have ha : raw23069step2 = (fun i j => raw23069step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23069step2 raw23069step1; decide +kernel
      have hl : raw23069step2Labels = raw23069step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23069step1 raw23069step1Labels permutation9 permutation3
    _ = mixedMoment B node546 node546Labels := by rfl

def raw23070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23070Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23070step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23070step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![3, -3, 0], ![2, 0, -2]]
def raw23070step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23070step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw23070step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23070 raw23070Labels = mixedMoment B node937 node937Labels := by
  calc
    mixedMoment B raw23070 raw23070Labels = mixedMoment B raw23070step0 raw23070step0Labels := by
      have hz : ∀ j, raw23070 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23070step0 = (fun i j => raw23070 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23070step0 raw23070; decide +kernel
      have hl : raw23070step0Labels = raw23070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23070 raw23070Labels permutation434 hz
    mixedMoment B raw23070step0 raw23070step0Labels = mixedMoment B raw23070step1 raw23070step1Labels := by
      have hz : ∀ j, raw23070step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23070step1 = (fun i j => raw23070step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23070step1 raw23070step0; decide +kernel
      have hl : raw23070step1Labels = raw23070step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23070step0 raw23070step0Labels permutation80 hz
    mixedMoment B raw23070step1 raw23070step1Labels = mixedMoment B raw23070step2 raw23070step2Labels := by
      have ha : raw23070step2 = (fun i j => raw23070step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23070step2 raw23070step1; decide +kernel
      have hl : raw23070step2Labels = raw23070step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23070step1 raw23070step1Labels permutation9 permutation3
    _ = mixedMoment B node937 node937Labels := by rfl

def raw23071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23071Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23071step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23071step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23071 raw23071Labels = mixedMoment B node872 node872Labels := by
  calc
    mixedMoment B raw23071 raw23071Labels = mixedMoment B raw23071step0 raw23071step0Labels := by
      have hz : ∀ j, raw23071 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23071step0 = (fun i j => raw23071 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23071step0 raw23071; decide +kernel
      have hl : raw23071step0Labels = raw23071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23071 raw23071Labels permutation434 hz
    mixedMoment B raw23071step0 raw23071step0Labels = mixedMoment B raw23071step1 raw23071step1Labels := by
      have ha : raw23071step1 = (fun i j => raw23071step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23071step1 raw23071step0; decide +kernel
      have hl : raw23071step1Labels = raw23071step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23071step0 raw23071step0Labels permutation39 permutation3
    _ = mixedMoment B node872 node872Labels := by rfl

def raw23072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23072Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw23072step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23072step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw23072step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23072 raw23072Labels = mixedMoment B node872 node872Labels := by
  calc
    mixedMoment B raw23072 raw23072Labels = mixedMoment B raw23072step0 raw23072step0Labels := by
      have hz : ∀ j, raw23072 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23072step0 = (fun i j => raw23072 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23072step0 raw23072; decide +kernel
      have hl : raw23072step0Labels = raw23072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23072 raw23072Labels permutation346 hz
    mixedMoment B raw23072step0 raw23072step0Labels = mixedMoment B raw23072step1 raw23072step1Labels := by
      have ha : raw23072step1 = (fun i j => raw23072step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23072step1 raw23072step0; decide +kernel
      have hl : raw23072step1Labels = raw23072step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23072step0 raw23072step0Labels permutation39 permutation3
    _ = mixedMoment B node872 node872Labels := by rfl

def raw23073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw23073Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw23073step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23073step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![3, -3, 0], ![1, 1, -2]]
def raw23073step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23073step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw23073step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23073 raw23073Labels = mixedMoment B node1037 node1037Labels := by
  calc
    mixedMoment B raw23073 raw23073Labels = mixedMoment B raw23073step0 raw23073step0Labels := by
      have hz : ∀ j, raw23073 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23073step0 = (fun i j => raw23073 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23073step0 raw23073; decide +kernel
      have hl : raw23073step0Labels = raw23073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23073 raw23073Labels permutation434 hz
    mixedMoment B raw23073step0 raw23073step0Labels = mixedMoment B raw23073step1 raw23073step1Labels := by
      have hz : ∀ j, raw23073step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23073step1 = (fun i j => raw23073step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23073step1 raw23073step0; decide +kernel
      have hl : raw23073step1Labels = raw23073step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23073step0 raw23073step0Labels permutation80 hz
    mixedMoment B raw23073step1 raw23073step1Labels = mixedMoment B raw23073step2 raw23073step2Labels := by
      have ha : raw23073step2 = (fun i j => raw23073step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23073step2 raw23073step1; decide +kernel
      have hl : raw23073step2Labels = raw23073step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23073step1 raw23073step1Labels permutation9 permutation3
    _ = mixedMoment B node1037 node1037Labels := by rfl

def raw23074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw23074Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw23074step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23074step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw23074step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23074step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23074step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23074 raw23074Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw23074 raw23074Labels = mixedMoment B raw23074step0 raw23074step0Labels := by
      have hz : ∀ j, raw23074 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23074step0 = (fun i j => raw23074 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23074step0 raw23074; decide +kernel
      have hl : raw23074step0Labels = raw23074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23074 raw23074Labels permutation434 hz
    mixedMoment B raw23074step0 raw23074step0Labels = mixedMoment B raw23074step1 raw23074step1Labels := by
      have hz : ∀ j, raw23074step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23074step1 = (fun i j => raw23074step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23074step1 raw23074step0; decide +kernel
      have hl : raw23074step1Labels = raw23074step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23074step0 raw23074step0Labels permutation80 hz
    mixedMoment B raw23074step1 raw23074step1Labels = mixedMoment B raw23074step2 raw23074step2Labels := by
      have ha : raw23074step2 = (fun i j => raw23074step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23074step2 raw23074step1; decide +kernel
      have hl : raw23074step2Labels = raw23074step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23074step1 raw23074step1Labels permutation8 permutation3
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw23075 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23075step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23075step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23075step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23075step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23075 raw23075Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw23075 raw23075Labels = mixedMoment B raw23075step0 raw23075step0Labels := by
      have hz : ∀ j, raw23075 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23075step0 = (fun i j => raw23075 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23075step0 raw23075; decide +kernel
      have hl : raw23075step0Labels = raw23075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23075 raw23075Labels permutation434 hz
    mixedMoment B raw23075step0 raw23075step0Labels = mixedMoment B raw23075step1 raw23075step1Labels := by
      have ha : raw23075step1 = (fun i j => raw23075step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23075step1 raw23075step0; decide +kernel
      have hl : raw23075step1Labels = raw23075step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23075step0 raw23075step0Labels permutation39 permutation6
    mixedMoment B raw23075step1 raw23075step1Labels = mixedMoment B raw23075step2 raw23075step2Labels := by
      have ha : raw23075step2 = raw23075step1 := by apply Matrix.ext; unfold raw23075step2 raw23075step1; decide +kernel
      have hl : raw23075step1Labels = labelEmbedding9 ∘ raw23075step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23075step1 raw23075step1Labels raw23075step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4592 node4592Labels := by rfl

def raw23076 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23076step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23076step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23076step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23076step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw23076step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw23076step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw23076step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23076 raw23076Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw23076 raw23076Labels = mixedMoment B raw23076step0 raw23076step0Labels := by
      have hz : ∀ j, raw23076 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23076step0 = (fun i j => raw23076 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23076step0 raw23076; decide +kernel
      have hl : raw23076step0Labels = raw23076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23076 raw23076Labels permutation434 hz
    mixedMoment B raw23076step0 raw23076step0Labels = mixedMoment B raw23076step1 raw23076step1Labels := by
      have hz : ∀ j, raw23076step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23076step1 = (fun i j => raw23076step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23076step1 raw23076step0; decide +kernel
      have hl : raw23076step1Labels = raw23076step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23076step0 raw23076step0Labels permutation80 hz
    mixedMoment B raw23076step1 raw23076step1Labels = mixedMoment B raw23076step2 raw23076step2Labels := by
      have ha : raw23076step2 = (fun i j => raw23076step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23076step2 raw23076step1; decide +kernel
      have hl : raw23076step2Labels = raw23076step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23076step1 raw23076step1Labels permutation8 permutation7
    mixedMoment B raw23076step2 raw23076step2Labels = mixedMoment B raw23076step3 raw23076step3Labels := by
      have ha : raw23076step3 = raw23076step2 := by apply Matrix.ext; unfold raw23076step3 raw23076step2; decide +kernel
      have hl : raw23076step2Labels = labelEmbedding10 ∘ raw23076step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23076step2 raw23076step2Labels raw23076step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4611 node4611Labels := by rfl

def raw23077 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23077step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23077step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23077step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw23077step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23077step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23077step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw23077step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23077step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23077 raw23077Labels = mixedMoment B node4278 node4278Labels := by
  calc
    mixedMoment B raw23077 raw23077Labels = mixedMoment B raw23077step0 raw23077step0Labels := by
      have hz : ∀ j, raw23077 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23077step0 = (fun i j => raw23077 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23077step0 raw23077; decide +kernel
      have hl : raw23077step0Labels = raw23077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23077 raw23077Labels permutation434 hz
    mixedMoment B raw23077step0 raw23077step0Labels = mixedMoment B raw23077step1 raw23077step1Labels := by
      have hz : ∀ j, raw23077step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23077step1 = (fun i j => raw23077step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23077step1 raw23077step0; decide +kernel
      have hl : raw23077step1Labels = raw23077step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23077step0 raw23077step0Labels permutation80 hz
    mixedMoment B raw23077step1 raw23077step1Labels = mixedMoment B raw23077step2 raw23077step2Labels := by
      have ha : raw23077step2 = (fun i j => raw23077step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw23077step2 raw23077step1; decide +kernel
      have hl : raw23077step2Labels = raw23077step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23077step1 raw23077step1Labels permutation12 permutation4
    mixedMoment B raw23077step2 raw23077step2Labels = mixedMoment B raw23077step3 raw23077step3Labels := by
      have ha : raw23077step3 = -raw23077step2 := by apply Matrix.ext; change ∀ i j, raw23077step3 i j = -(raw23077step2 i j); unfold raw23077step3 raw23077step2; decide +kernel
      have hl : raw23077step3Labels = raw23077step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23077step3 raw23077step3Labels = mixedMoment B raw23077step4 raw23077step4Labels := by
      have ha : raw23077step4 = raw23077step3 := by apply Matrix.ext; unfold raw23077step4 raw23077step3; decide +kernel
      have hl : raw23077step3Labels = labelEmbedding7 ∘ raw23077step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23077step3 raw23077step3Labels raw23077step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4278 node4278Labels := by rfl

def raw23078 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23078step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23078step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23078step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23078 raw23078Labels = mixedMoment B node4411 node4411Labels := by
  calc
    mixedMoment B raw23078 raw23078Labels = mixedMoment B raw23078step0 raw23078step0Labels := by
      have hz : ∀ j, raw23078 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23078step0 = (fun i j => raw23078 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23078step0 raw23078; decide +kernel
      have hl : raw23078step0Labels = raw23078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23078 raw23078Labels permutation434 hz
    mixedMoment B raw23078step0 raw23078step0Labels = mixedMoment B raw23078step1 raw23078step1Labels := by
      have ha : raw23078step1 = (fun i j => raw23078step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23078step1 raw23078step0; decide +kernel
      have hl : raw23078step1Labels = raw23078step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23078step0 raw23078step0Labels permutation39 permutation6
    mixedMoment B raw23078step1 raw23078step1Labels = mixedMoment B raw23078step2 raw23078step2Labels := by
      have ha : raw23078step2 = raw23078step1 := by apply Matrix.ext; unfold raw23078step2 raw23078step1; decide +kernel
      have hl : raw23078step1Labels = labelEmbedding9 ∘ raw23078step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23078step1 raw23078step1Labels raw23078step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4411 node4411Labels := by rfl

def raw23079 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23079step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23079step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23079step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23079step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23079 raw23079Labels = mixedMoment B node4411 node4411Labels := by
  calc
    mixedMoment B raw23079 raw23079Labels = mixedMoment B raw23079step0 raw23079step0Labels := by
      have hz : ∀ j, raw23079 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23079step0 = (fun i j => raw23079 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23079step0 raw23079; decide +kernel
      have hl : raw23079step0Labels = raw23079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23079 raw23079Labels permutation346 hz
    mixedMoment B raw23079step0 raw23079step0Labels = mixedMoment B raw23079step1 raw23079step1Labels := by
      have ha : raw23079step1 = (fun i j => raw23079step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23079step1 raw23079step0; decide +kernel
      have hl : raw23079step1Labels = raw23079step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23079step0 raw23079step0Labels permutation39 permutation6
    mixedMoment B raw23079step1 raw23079step1Labels = mixedMoment B raw23079step2 raw23079step2Labels := by
      have ha : raw23079step2 = raw23079step1 := by apply Matrix.ext; unfold raw23079step2 raw23079step1; decide +kernel
      have hl : raw23079step1Labels = labelEmbedding9 ∘ raw23079step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23079step1 raw23079step1Labels raw23079step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4411 node4411Labels := by rfl

def raw23080 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23080step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23080step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23080step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23080step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23080step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23080step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23080 raw23080Labels = mixedMoment B node4480 node4480Labels := by
  calc
    mixedMoment B raw23080 raw23080Labels = mixedMoment B raw23080step0 raw23080step0Labels := by
      have hz : ∀ j, raw23080 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23080step0 = (fun i j => raw23080 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23080step0 raw23080; decide +kernel
      have hl : raw23080step0Labels = raw23080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23080 raw23080Labels permutation434 hz
    mixedMoment B raw23080step0 raw23080step0Labels = mixedMoment B raw23080step1 raw23080step1Labels := by
      have hz : ∀ j, raw23080step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23080step1 = (fun i j => raw23080step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23080step1 raw23080step0; decide +kernel
      have hl : raw23080step1Labels = raw23080step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23080step0 raw23080step0Labels permutation80 hz
    mixedMoment B raw23080step1 raw23080step1Labels = mixedMoment B raw23080step2 raw23080step2Labels := by
      have ha : raw23080step2 = (fun i j => raw23080step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23080step2 raw23080step1; decide +kernel
      have hl : raw23080step2Labels = raw23080step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23080step1 raw23080step1Labels permutation9 permutation6
    mixedMoment B raw23080step2 raw23080step2Labels = mixedMoment B raw23080step3 raw23080step3Labels := by
      have ha : raw23080step3 = raw23080step2 := by apply Matrix.ext; unfold raw23080step3 raw23080step2; decide +kernel
      have hl : raw23080step2Labels = labelEmbedding9 ∘ raw23080step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23080step2 raw23080step2Labels raw23080step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4480 node4480Labels := by rfl

def raw23081 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23081step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23081step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23081step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw23081step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23081step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw23081step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23081 raw23081Labels = mixedMoment B node4479 node4479Labels := by
  calc
    mixedMoment B raw23081 raw23081Labels = mixedMoment B raw23081step0 raw23081step0Labels := by
      have hz : ∀ j, raw23081 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23081step0 = (fun i j => raw23081 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23081step0 raw23081; decide +kernel
      have hl : raw23081step0Labels = raw23081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23081 raw23081Labels permutation434 hz
    mixedMoment B raw23081step0 raw23081step0Labels = mixedMoment B raw23081step1 raw23081step1Labels := by
      have hz : ∀ j, raw23081step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23081step1 = (fun i j => raw23081step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23081step1 raw23081step0; decide +kernel
      have hl : raw23081step1Labels = raw23081step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23081step0 raw23081step0Labels permutation80 hz
    mixedMoment B raw23081step1 raw23081step1Labels = mixedMoment B raw23081step2 raw23081step2Labels := by
      have ha : raw23081step2 = (fun i j => raw23081step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23081step2 raw23081step1; decide +kernel
      have hl : raw23081step2Labels = raw23081step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23081step1 raw23081step1Labels permutation9 permutation6
    mixedMoment B raw23081step2 raw23081step2Labels = mixedMoment B raw23081step3 raw23081step3Labels := by
      have ha : raw23081step3 = raw23081step2 := by apply Matrix.ext; unfold raw23081step3 raw23081step2; decide +kernel
      have hl : raw23081step2Labels = labelEmbedding9 ∘ raw23081step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23081step2 raw23081step2Labels raw23081step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4479 node4479Labels := by rfl

def raw23082 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23082step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23082step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23082 raw23082Labels = mixedMoment B node4255 node4255Labels := by
  calc
    mixedMoment B raw23082 raw23082Labels = mixedMoment B raw23082step0 raw23082step0Labels := by
      have hz : ∀ j, raw23082 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23082step0 = (fun i j => raw23082 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23082step0 raw23082; decide +kernel
      have hl : raw23082step0Labels = raw23082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23082 raw23082Labels permutation434 hz
    mixedMoment B raw23082step0 raw23082step0Labels = mixedMoment B raw23082step1 raw23082step1Labels := by
      have ha : raw23082step1 = (fun i j => raw23082step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23082step1 raw23082step0; decide +kernel
      have hl : raw23082step1Labels = raw23082step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23082step0 raw23082step0Labels permutation33 permutation6
    mixedMoment B raw23082step1 raw23082step1Labels = mixedMoment B raw23082step2 raw23082step2Labels := by
      have ha : raw23082step2 = raw23082step1 := by apply Matrix.ext; unfold raw23082step2 raw23082step1; decide +kernel
      have hl : raw23082step1Labels = labelEmbedding9 ∘ raw23082step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23082step1 raw23082step1Labels raw23082step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4255 node4255Labels := by rfl

def raw23083 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23083step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23083step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23083step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23083step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23083step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23083 raw23083Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw23083 raw23083Labels = mixedMoment B raw23083step0 raw23083step0Labels := by
      have hz : ∀ j, raw23083 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23083step0 = (fun i j => raw23083 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23083step0 raw23083; decide +kernel
      have hl : raw23083step0Labels = raw23083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23083 raw23083Labels permutation434 hz
    mixedMoment B raw23083step0 raw23083step0Labels = mixedMoment B raw23083step1 raw23083step1Labels := by
      have hz : ∀ j, raw23083step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23083step1 = (fun i j => raw23083step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23083step1 raw23083step0; decide +kernel
      have hl : raw23083step1Labels = raw23083step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23083step0 raw23083step0Labels permutation56 hz
    mixedMoment B raw23083step1 raw23083step1Labels = mixedMoment B raw23083step2 raw23083step2Labels := by
      have ha : raw23083step2 = (fun i j => raw23083step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23083step2 raw23083step1; decide +kernel
      have hl : raw23083step2Labels = raw23083step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23083step1 raw23083step1Labels permutation9 permutation6
    mixedMoment B raw23083step2 raw23083step2Labels = mixedMoment B raw23083step3 raw23083step3Labels := by
      have ha : raw23083step3 = raw23083step2 := by apply Matrix.ext; unfold raw23083step3 raw23083step2; decide +kernel
      have hl : raw23083step2Labels = labelEmbedding9 ∘ raw23083step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23083step2 raw23083step2Labels raw23083step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

def raw23084 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23084step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23084step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23084step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23084 raw23084Labels = mixedMoment B node4392 node4392Labels := by
  calc
    mixedMoment B raw23084 raw23084Labels = mixedMoment B raw23084step0 raw23084step0Labels := by
      have ha : raw23084step0 = (fun i j => raw23084 (permutation201 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23084step0 raw23084; decide +kernel
      have hl : raw23084step0Labels = raw23084Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23084 raw23084Labels permutation201 permutation6
    mixedMoment B raw23084step0 raw23084step0Labels = mixedMoment B raw23084step1 raw23084step1Labels := by
      have ha : raw23084step1 = raw23084step0 := by apply Matrix.ext; unfold raw23084step1 raw23084step0; decide +kernel
      have hl : raw23084step0Labels = labelEmbedding9 ∘ raw23084step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23084step0 raw23084step0Labels raw23084step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4392 node4392Labels := by rfl

def raw23085 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23085step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23085step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23085step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23085 raw23085Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw23085 raw23085Labels = mixedMoment B raw23085step0 raw23085step0Labels := by
      have hz : ∀ j, raw23085 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23085step0 = (fun i j => raw23085 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23085step0 raw23085; decide +kernel
      have hl : raw23085step0Labels = raw23085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23085 raw23085Labels permutation434 hz
    mixedMoment B raw23085step0 raw23085step0Labels = mixedMoment B raw23085step1 raw23085step1Labels := by
      have ha : raw23085step1 = (fun i j => raw23085step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23085step1 raw23085step0; decide +kernel
      have hl : raw23085step1Labels = raw23085step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23085step0 raw23085step0Labels permutation33 permutation6
    mixedMoment B raw23085step1 raw23085step1Labels = mixedMoment B raw23085step2 raw23085step2Labels := by
      have ha : raw23085step2 = raw23085step1 := by apply Matrix.ext; unfold raw23085step2 raw23085step1; decide +kernel
      have hl : raw23085step1Labels = labelEmbedding9 ∘ raw23085step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23085step1 raw23085step1Labels raw23085step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4444 node4444Labels := by rfl

def raw23086 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23086step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23086step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23086step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23086 raw23086Labels = mixedMoment B node4443 node4443Labels := by
  calc
    mixedMoment B raw23086 raw23086Labels = mixedMoment B raw23086step0 raw23086step0Labels := by
      have hz : ∀ j, raw23086 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23086step0 = (fun i j => raw23086 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23086step0 raw23086; decide +kernel
      have hl : raw23086step0Labels = raw23086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23086 raw23086Labels permutation434 hz
    mixedMoment B raw23086step0 raw23086step0Labels = mixedMoment B raw23086step1 raw23086step1Labels := by
      have ha : raw23086step1 = (fun i j => raw23086step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23086step1 raw23086step0; decide +kernel
      have hl : raw23086step1Labels = raw23086step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23086step0 raw23086step0Labels permutation33 permutation6
    mixedMoment B raw23086step1 raw23086step1Labels = mixedMoment B raw23086step2 raw23086step2Labels := by
      have ha : raw23086step2 = raw23086step1 := by apply Matrix.ext; unfold raw23086step2 raw23086step1; decide +kernel
      have hl : raw23086step1Labels = labelEmbedding9 ∘ raw23086step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23086step1 raw23086step1Labels raw23086step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4443 node4443Labels := by rfl

def raw23087 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23087step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23087step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23087 raw23087Labels = mixedMoment B node4255 node4255Labels := by
  calc
    mixedMoment B raw23087 raw23087Labels = mixedMoment B raw23087step0 raw23087step0Labels := by
      have hz : ∀ j, raw23087 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23087step0 = (fun i j => raw23087 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23087step0 raw23087; decide +kernel
      have hl : raw23087step0Labels = raw23087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23087 raw23087Labels permutation346 hz
    mixedMoment B raw23087step0 raw23087step0Labels = mixedMoment B raw23087step1 raw23087step1Labels := by
      have ha : raw23087step1 = (fun i j => raw23087step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23087step1 raw23087step0; decide +kernel
      have hl : raw23087step1Labels = raw23087step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23087step0 raw23087step0Labels permutation33 permutation6
    mixedMoment B raw23087step1 raw23087step1Labels = mixedMoment B raw23087step2 raw23087step2Labels := by
      have ha : raw23087step2 = raw23087step1 := by apply Matrix.ext; unfold raw23087step2 raw23087step1; decide +kernel
      have hl : raw23087step1Labels = labelEmbedding9 ∘ raw23087step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23087step1 raw23087step1Labels raw23087step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4255 node4255Labels := by rfl

def raw23088 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23088step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23088step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23088step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23088step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23088 raw23088Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw23088 raw23088Labels = mixedMoment B raw23088step0 raw23088step0Labels := by
      have hz : ∀ j, raw23088 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23088step0 = (fun i j => raw23088 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23088step0 raw23088; decide +kernel
      have hl : raw23088step0Labels = raw23088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23088 raw23088Labels permutation346 hz
    mixedMoment B raw23088step0 raw23088step0Labels = mixedMoment B raw23088step1 raw23088step1Labels := by
      have hz : ∀ j, raw23088step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23088step1 = (fun i j => raw23088step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23088step1 raw23088step0; decide +kernel
      have hl : raw23088step1Labels = raw23088step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23088step0 raw23088step0Labels permutation56 hz
    mixedMoment B raw23088step1 raw23088step1Labels = mixedMoment B raw23088step2 raw23088step2Labels := by
      have ha : raw23088step2 = (fun i j => raw23088step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23088step2 raw23088step1; decide +kernel
      have hl : raw23088step2Labels = raw23088step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23088step1 raw23088step1Labels permutation9 permutation6
    mixedMoment B raw23088step2 raw23088step2Labels = mixedMoment B raw23088step3 raw23088step3Labels := by
      have ha : raw23088step3 = raw23088step2 := by apply Matrix.ext; unfold raw23088step3 raw23088step2; decide +kernel
      have hl : raw23088step2Labels = labelEmbedding9 ∘ raw23088step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23088step2 raw23088step2Labels raw23088step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

def raw23089 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23089step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23089step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23089 raw23089Labels = mixedMoment B node4392 node4392Labels := by
  calc
    mixedMoment B raw23089 raw23089Labels = mixedMoment B raw23089step0 raw23089step0Labels := by
      have ha : raw23089step0 = (fun i j => raw23089 (permutation177 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23089step0 raw23089; decide +kernel
      have hl : raw23089step0Labels = raw23089Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23089 raw23089Labels permutation177 permutation6
    mixedMoment B raw23089step0 raw23089step0Labels = mixedMoment B raw23089step1 raw23089step1Labels := by
      have ha : raw23089step1 = raw23089step0 := by apply Matrix.ext; unfold raw23089step1 raw23089step0; decide +kernel
      have hl : raw23089step0Labels = labelEmbedding9 ∘ raw23089step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23089step0 raw23089step0Labels raw23089step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4392 node4392Labels := by rfl

def raw23090 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23090step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23090step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23090step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23090 raw23090Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw23090 raw23090Labels = mixedMoment B raw23090step0 raw23090step0Labels := by
      have hz : ∀ j, raw23090 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23090step0 = (fun i j => raw23090 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23090step0 raw23090; decide +kernel
      have hl : raw23090step0Labels = raw23090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23090 raw23090Labels permutation346 hz
    mixedMoment B raw23090step0 raw23090step0Labels = mixedMoment B raw23090step1 raw23090step1Labels := by
      have ha : raw23090step1 = (fun i j => raw23090step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23090step1 raw23090step0; decide +kernel
      have hl : raw23090step1Labels = raw23090step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23090step0 raw23090step0Labels permutation33 permutation6
    mixedMoment B raw23090step1 raw23090step1Labels = mixedMoment B raw23090step2 raw23090step2Labels := by
      have ha : raw23090step2 = raw23090step1 := by apply Matrix.ext; unfold raw23090step2 raw23090step1; decide +kernel
      have hl : raw23090step1Labels = labelEmbedding9 ∘ raw23090step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23090step1 raw23090step1Labels raw23090step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4444 node4444Labels := by rfl

def raw23091 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23091step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23091step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23091step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23091step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23091 raw23091Labels = mixedMoment B node4443 node4443Labels := by
  calc
    mixedMoment B raw23091 raw23091Labels = mixedMoment B raw23091step0 raw23091step0Labels := by
      have hz : ∀ j, raw23091 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23091step0 = (fun i j => raw23091 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23091step0 raw23091; decide +kernel
      have hl : raw23091step0Labels = raw23091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23091 raw23091Labels permutation346 hz
    mixedMoment B raw23091step0 raw23091step0Labels = mixedMoment B raw23091step1 raw23091step1Labels := by
      have ha : raw23091step1 = (fun i j => raw23091step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23091step1 raw23091step0; decide +kernel
      have hl : raw23091step1Labels = raw23091step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23091step0 raw23091step0Labels permutation33 permutation6
    mixedMoment B raw23091step1 raw23091step1Labels = mixedMoment B raw23091step2 raw23091step2Labels := by
      have ha : raw23091step2 = raw23091step1 := by apply Matrix.ext; unfold raw23091step2 raw23091step1; decide +kernel
      have hl : raw23091step1Labels = labelEmbedding9 ∘ raw23091step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23091step1 raw23091step1Labels raw23091step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4443 node4443Labels := by rfl

def raw23092 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23092step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23092step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23092step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23092step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23092 raw23092Labels = mixedMoment B node4272 node4272Labels := by
  calc
    mixedMoment B raw23092 raw23092Labels = mixedMoment B raw23092step0 raw23092step0Labels := by
      have hz : ∀ j, raw23092 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23092step0 = (fun i j => raw23092 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23092step0 raw23092; decide +kernel
      have hl : raw23092step0Labels = raw23092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23092 raw23092Labels permutation434 hz
    mixedMoment B raw23092step0 raw23092step0Labels = mixedMoment B raw23092step1 raw23092step1Labels := by
      have hz : ∀ j, raw23092step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23092step1 = (fun i j => raw23092step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23092step1 raw23092step0; decide +kernel
      have hl : raw23092step1Labels = raw23092step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23092step0 raw23092step0Labels permutation80 hz
    mixedMoment B raw23092step1 raw23092step1Labels = mixedMoment B raw23092step2 raw23092step2Labels := by
      have ha : raw23092step2 = (fun i j => raw23092step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23092step2 raw23092step1; decide +kernel
      have hl : raw23092step2Labels = raw23092step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23092step1 raw23092step1Labels permutation9 permutation6
    mixedMoment B raw23092step2 raw23092step2Labels = mixedMoment B raw23092step3 raw23092step3Labels := by
      have ha : raw23092step3 = raw23092step2 := by apply Matrix.ext; unfold raw23092step3 raw23092step2; decide +kernel
      have hl : raw23092step2Labels = labelEmbedding9 ∘ raw23092step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23092step2 raw23092step2Labels raw23092step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4272 node4272Labels := by rfl

def raw23093 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23093step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23093step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23093step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -3, 2], ![-2, 0, 2]]
def raw23093step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23093step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw23093step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23093step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw23093step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23093 raw23093Labels = mixedMoment B node4510 node4510Labels := by
  calc
    mixedMoment B raw23093 raw23093Labels = mixedMoment B raw23093step0 raw23093step0Labels := by
      have hz : ∀ j, raw23093 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23093step0 = (fun i j => raw23093 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23093step0 raw23093; decide +kernel
      have hl : raw23093step0Labels = raw23093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23093 raw23093Labels permutation434 hz
    mixedMoment B raw23093step0 raw23093step0Labels = mixedMoment B raw23093step1 raw23093step1Labels := by
      have hz : ∀ j, raw23093step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23093step1 = (fun i j => raw23093step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23093step1 raw23093step0; decide +kernel
      have hl : raw23093step1Labels = raw23093step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23093step0 raw23093step0Labels permutation80 hz
    mixedMoment B raw23093step1 raw23093step1Labels = mixedMoment B raw23093step2 raw23093step2Labels := by
      have hz : ∀ j, raw23093step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23093step2 = (fun i j => raw23093step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23093step2 raw23093step1; decide +kernel
      have hl : raw23093step2Labels = raw23093step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23093step1 raw23093step1Labels permutation14 hz
    mixedMoment B raw23093step2 raw23093step2Labels = mixedMoment B raw23093step3 raw23093step3Labels := by
      have ha : raw23093step3 = (fun i j => raw23093step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23093step3 raw23093step2; decide +kernel
      have hl : raw23093step3Labels = raw23093step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23093step2 raw23093step2Labels permutation3 permutation6
    mixedMoment B raw23093step3 raw23093step3Labels = mixedMoment B raw23093step4 raw23093step4Labels := by
      have ha : raw23093step4 = raw23093step3 := by apply Matrix.ext; unfold raw23093step4 raw23093step3; decide +kernel
      have hl : raw23093step3Labels = labelEmbedding9 ∘ raw23093step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23093step3 raw23093step3Labels raw23093step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4510 node4510Labels := by rfl

def raw23094 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23094step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23094step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23094step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23094step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23094 raw23094Labels = mixedMoment B node4403 node4403Labels := by
  calc
    mixedMoment B raw23094 raw23094Labels = mixedMoment B raw23094step0 raw23094step0Labels := by
      have hz : ∀ j, raw23094 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23094step0 = (fun i j => raw23094 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23094step0 raw23094; decide +kernel
      have hl : raw23094step0Labels = raw23094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23094 raw23094Labels permutation434 hz
    mixedMoment B raw23094step0 raw23094step0Labels = mixedMoment B raw23094step1 raw23094step1Labels := by
      have ha : raw23094step1 = (fun i j => raw23094step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23094step1 raw23094step0; decide +kernel
      have hl : raw23094step1Labels = raw23094step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23094step0 raw23094step0Labels permutation39 permutation6
    mixedMoment B raw23094step1 raw23094step1Labels = mixedMoment B raw23094step2 raw23094step2Labels := by
      have ha : raw23094step2 = raw23094step1 := by apply Matrix.ext; unfold raw23094step2 raw23094step1; decide +kernel
      have hl : raw23094step1Labels = labelEmbedding9 ∘ raw23094step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23094step1 raw23094step1Labels raw23094step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4403 node4403Labels := by rfl

def raw23095 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23095step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23095step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23095step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23095step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23095 raw23095Labels = mixedMoment B node4403 node4403Labels := by
  calc
    mixedMoment B raw23095 raw23095Labels = mixedMoment B raw23095step0 raw23095step0Labels := by
      have hz : ∀ j, raw23095 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23095step0 = (fun i j => raw23095 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23095step0 raw23095; decide +kernel
      have hl : raw23095step0Labels = raw23095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23095 raw23095Labels permutation346 hz
    mixedMoment B raw23095step0 raw23095step0Labels = mixedMoment B raw23095step1 raw23095step1Labels := by
      have ha : raw23095step1 = (fun i j => raw23095step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23095step1 raw23095step0; decide +kernel
      have hl : raw23095step1Labels = raw23095step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23095step0 raw23095step0Labels permutation39 permutation6
    mixedMoment B raw23095step1 raw23095step1Labels = mixedMoment B raw23095step2 raw23095step2Labels := by
      have ha : raw23095step2 = raw23095step1 := by apply Matrix.ext; unfold raw23095step2 raw23095step1; decide +kernel
      have hl : raw23095step1Labels = labelEmbedding9 ∘ raw23095step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23095step1 raw23095step1Labels raw23095step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4403 node4403Labels := by rfl

def raw23096 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23096step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23096step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23096step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23096step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw23096step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23096step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw23096step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23096 raw23096Labels = mixedMoment B node4465 node4465Labels := by
  calc
    mixedMoment B raw23096 raw23096Labels = mixedMoment B raw23096step0 raw23096step0Labels := by
      have hz : ∀ j, raw23096 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23096step0 = (fun i j => raw23096 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23096step0 raw23096; decide +kernel
      have hl : raw23096step0Labels = raw23096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23096 raw23096Labels permutation434 hz
    mixedMoment B raw23096step0 raw23096step0Labels = mixedMoment B raw23096step1 raw23096step1Labels := by
      have hz : ∀ j, raw23096step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23096step1 = (fun i j => raw23096step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23096step1 raw23096step0; decide +kernel
      have hl : raw23096step1Labels = raw23096step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23096step0 raw23096step0Labels permutation80 hz
    mixedMoment B raw23096step1 raw23096step1Labels = mixedMoment B raw23096step2 raw23096step2Labels := by
      have ha : raw23096step2 = (fun i j => raw23096step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23096step2 raw23096step1; decide +kernel
      have hl : raw23096step2Labels = raw23096step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23096step1 raw23096step1Labels permutation9 permutation6
    mixedMoment B raw23096step2 raw23096step2Labels = mixedMoment B raw23096step3 raw23096step3Labels := by
      have ha : raw23096step3 = raw23096step2 := by apply Matrix.ext; unfold raw23096step3 raw23096step2; decide +kernel
      have hl : raw23096step2Labels = labelEmbedding9 ∘ raw23096step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23096step2 raw23096step2Labels raw23096step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4465 node4465Labels := by rfl

def raw23097 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23097step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23097step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23097step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23097step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23097step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23097step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23097 raw23097Labels = mixedMoment B node4273 node4273Labels := by
  calc
    mixedMoment B raw23097 raw23097Labels = mixedMoment B raw23097step0 raw23097step0Labels := by
      have hz : ∀ j, raw23097 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23097step0 = (fun i j => raw23097 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23097step0 raw23097; decide +kernel
      have hl : raw23097step0Labels = raw23097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23097 raw23097Labels permutation434 hz
    mixedMoment B raw23097step0 raw23097step0Labels = mixedMoment B raw23097step1 raw23097step1Labels := by
      have hz : ∀ j, raw23097step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23097step1 = (fun i j => raw23097step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23097step1 raw23097step0; decide +kernel
      have hl : raw23097step1Labels = raw23097step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23097step0 raw23097step0Labels permutation80 hz
    mixedMoment B raw23097step1 raw23097step1Labels = mixedMoment B raw23097step2 raw23097step2Labels := by
      have ha : raw23097step2 = (fun i j => raw23097step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23097step2 raw23097step1; decide +kernel
      have hl : raw23097step2Labels = raw23097step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23097step1 raw23097step1Labels permutation9 permutation6
    mixedMoment B raw23097step2 raw23097step2Labels = mixedMoment B raw23097step3 raw23097step3Labels := by
      have ha : raw23097step3 = raw23097step2 := by apply Matrix.ext; unfold raw23097step3 raw23097step2; decide +kernel
      have hl : raw23097step2Labels = labelEmbedding9 ∘ raw23097step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23097step2 raw23097step2Labels raw23097step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4273 node4273Labels := by rfl

def raw23098 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23098step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23098step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw23098step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23098step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23098 raw23098Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw23098 raw23098Labels = mixedMoment B raw23098step0 raw23098step0Labels := by
      have hz : ∀ j, raw23098 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23098step0 = (fun i j => raw23098 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23098step0 raw23098; decide +kernel
      have hl : raw23098step0Labels = raw23098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23098 raw23098Labels permutation434 hz
    mixedMoment B raw23098step0 raw23098step0Labels = mixedMoment B raw23098step1 raw23098step1Labels := by
      have ha : raw23098step1 = (fun i j => raw23098step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23098step1 raw23098step0; decide +kernel
      have hl : raw23098step1Labels = raw23098step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23098step0 raw23098step0Labels permutation39 permutation6
    mixedMoment B raw23098step1 raw23098step1Labels = mixedMoment B raw23098step2 raw23098step2Labels := by
      have ha : raw23098step2 = raw23098step1 := by apply Matrix.ext; unfold raw23098step2 raw23098step1; decide +kernel
      have hl : raw23098step1Labels = labelEmbedding9 ∘ raw23098step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23098step1 raw23098step1Labels raw23098step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

def raw23099 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23099Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23099step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23099 raw23099Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw23099 raw23099Labels = mixedMoment B raw23099step0 raw23099step0Labels := by
      have hz : ∀ j, raw23099 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23099step0 = (fun i j => raw23099 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23099step0 raw23099; decide +kernel
      have hl : raw23099step0Labels = raw23099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23099 raw23099Labels permutation434 hz
    mixedMoment B raw23099step0 raw23099step0Labels = mixedMoment B raw23099step1 raw23099step1Labels := by
      have ha : raw23099step1 = (fun i j => raw23099step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23099step1 raw23099step0; decide +kernel
      have hl : raw23099step1Labels = raw23099step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23099step0 raw23099step0Labels permutation39 permutation6
    _ = mixedMoment B node1219 node1219Labels := by rfl

def raw23100 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23100Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23100step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23100step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23100step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23100step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23100 raw23100Labels = mixedMoment B node1273 node1273Labels := by
  calc
    mixedMoment B raw23100 raw23100Labels = mixedMoment B raw23100step0 raw23100step0Labels := by
      have hz : ∀ j, raw23100 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23100step0 = (fun i j => raw23100 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23100step0 raw23100; decide +kernel
      have hl : raw23100step0Labels = raw23100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23100 raw23100Labels permutation434 hz
    mixedMoment B raw23100step0 raw23100step0Labels = mixedMoment B raw23100step1 raw23100step1Labels := by
      have hz : ∀ j, raw23100step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23100step1 = (fun i j => raw23100step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23100step1 raw23100step0; decide +kernel
      have hl : raw23100step1Labels = raw23100step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23100step0 raw23100step0Labels permutation80 hz
    mixedMoment B raw23100step1 raw23100step1Labels = mixedMoment B raw23100step2 raw23100step2Labels := by
      have ha : raw23100step2 = (fun i j => raw23100step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23100step2 raw23100step1; decide +kernel
      have hl : raw23100step2Labels = raw23100step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23100step1 raw23100step1Labels permutation9 permutation6
    _ = mixedMoment B node1273 node1273Labels := by rfl

def raw23101 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23101Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23101step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23101step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23101step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23101step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23101 raw23101Labels = mixedMoment B node830 node830Labels := by
  calc
    mixedMoment B raw23101 raw23101Labels = mixedMoment B raw23101step0 raw23101step0Labels := by
      have hz : ∀ j, raw23101 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23101step0 = (fun i j => raw23101 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23101step0 raw23101; decide +kernel
      have hl : raw23101step0Labels = raw23101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23101 raw23101Labels permutation434 hz
    mixedMoment B raw23101step0 raw23101step0Labels = mixedMoment B raw23101step1 raw23101step1Labels := by
      have hz : ∀ j, raw23101step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23101step1 = (fun i j => raw23101step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23101step1 raw23101step0; decide +kernel
      have hl : raw23101step1Labels = raw23101step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23101step0 raw23101step0Labels permutation80 hz
    mixedMoment B raw23101step1 raw23101step1Labels = mixedMoment B raw23101step2 raw23101step2Labels := by
      have ha : raw23101step2 = (fun i j => raw23101step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23101step2 raw23101step1; decide +kernel
      have hl : raw23101step2Labels = raw23101step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23101step1 raw23101step1Labels permutation9 permutation6
    _ = mixedMoment B node830 node830Labels := by rfl

def raw23102 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23102Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23102step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23102step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23102 raw23102Labels = mixedMoment B node992 node992Labels := by
  calc
    mixedMoment B raw23102 raw23102Labels = mixedMoment B raw23102step0 raw23102step0Labels := by
      have hz : ∀ j, raw23102 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23102step0 = (fun i j => raw23102 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23102step0 raw23102; decide +kernel
      have hl : raw23102step0Labels = raw23102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23102 raw23102Labels permutation434 hz
    mixedMoment B raw23102step0 raw23102step0Labels = mixedMoment B raw23102step1 raw23102step1Labels := by
      have ha : raw23102step1 = (fun i j => raw23102step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23102step1 raw23102step0; decide +kernel
      have hl : raw23102step1Labels = raw23102step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23102step0 raw23102step0Labels permutation39 permutation6
    _ = mixedMoment B node992 node992Labels := by rfl

def raw23103 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23103Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23103step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw23103step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23103 raw23103Labels = mixedMoment B node992 node992Labels := by
  calc
    mixedMoment B raw23103 raw23103Labels = mixedMoment B raw23103step0 raw23103step0Labels := by
      have hz : ∀ j, raw23103 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23103step0 = (fun i j => raw23103 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23103step0 raw23103; decide +kernel
      have hl : raw23103step0Labels = raw23103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23103 raw23103Labels permutation346 hz
    mixedMoment B raw23103step0 raw23103step0Labels = mixedMoment B raw23103step1 raw23103step1Labels := by
      have ha : raw23103step1 = (fun i j => raw23103step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23103step1 raw23103step0; decide +kernel
      have hl : raw23103step1Labels = raw23103step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23103step0 raw23103step0Labels permutation39 permutation6
    _ = mixedMoment B node992 node992Labels := by rfl

def raw23104 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23104Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23104step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23104step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23104step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw23104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23104 raw23104Labels = mixedMoment B node1063 node1063Labels := by
  calc
    mixedMoment B raw23104 raw23104Labels = mixedMoment B raw23104step0 raw23104step0Labels := by
      have hz : ∀ j, raw23104 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23104step0 = (fun i j => raw23104 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23104step0 raw23104; decide +kernel
      have hl : raw23104step0Labels = raw23104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23104 raw23104Labels permutation434 hz
    mixedMoment B raw23104step0 raw23104step0Labels = mixedMoment B raw23104step1 raw23104step1Labels := by
      have hz : ∀ j, raw23104step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23104step1 = (fun i j => raw23104step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23104step1 raw23104step0; decide +kernel
      have hl : raw23104step1Labels = raw23104step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23104step0 raw23104step0Labels permutation80 hz
    mixedMoment B raw23104step1 raw23104step1Labels = mixedMoment B raw23104step2 raw23104step2Labels := by
      have ha : raw23104step2 = (fun i j => raw23104step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23104step2 raw23104step1; decide +kernel
      have hl : raw23104step2Labels = raw23104step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23104step1 raw23104step1Labels permutation9 permutation6
    _ = mixedMoment B node1063 node1063Labels := by rfl

def raw23105 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23105Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23105step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23105step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw23105step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23105 raw23105Labels = mixedMoment B node1062 node1062Labels := by
  calc
    mixedMoment B raw23105 raw23105Labels = mixedMoment B raw23105step0 raw23105step0Labels := by
      have hz : ∀ j, raw23105 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23105step0 = (fun i j => raw23105 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23105step0 raw23105; decide +kernel
      have hl : raw23105step0Labels = raw23105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23105 raw23105Labels permutation434 hz
    mixedMoment B raw23105step0 raw23105step0Labels = mixedMoment B raw23105step1 raw23105step1Labels := by
      have hz : ∀ j, raw23105step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23105step1 = (fun i j => raw23105step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23105step1 raw23105step0; decide +kernel
      have hl : raw23105step1Labels = raw23105step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23105step0 raw23105step0Labels permutation80 hz
    mixedMoment B raw23105step1 raw23105step1Labels = mixedMoment B raw23105step2 raw23105step2Labels := by
      have ha : raw23105step2 = (fun i j => raw23105step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23105step2 raw23105step1; decide +kernel
      have hl : raw23105step2Labels = raw23105step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23105step1 raw23105step1Labels permutation9 permutation6
    _ = mixedMoment B node1062 node1062Labels := by rfl

def raw23106 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23106Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23106step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23106step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23106 raw23106Labels = mixedMoment B node789 node789Labels := by
  calc
    mixedMoment B raw23106 raw23106Labels = mixedMoment B raw23106step0 raw23106step0Labels := by
      have hz : ∀ j, raw23106 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23106step0 = (fun i j => raw23106 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23106step0 raw23106; decide +kernel
      have hl : raw23106step0Labels = raw23106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23106 raw23106Labels permutation434 hz
    mixedMoment B raw23106step0 raw23106step0Labels = mixedMoment B raw23106step1 raw23106step1Labels := by
      have ha : raw23106step1 = (fun i j => raw23106step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23106step1 raw23106step0; decide +kernel
      have hl : raw23106step1Labels = raw23106step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23106step0 raw23106step0Labels permutation33 permutation6
    _ = mixedMoment B node789 node789Labels := by rfl

def raw23107 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23107Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23107step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23107step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23107step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23107step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23107step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23107 raw23107Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw23107 raw23107Labels = mixedMoment B raw23107step0 raw23107step0Labels := by
      have hz : ∀ j, raw23107 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23107step0 = (fun i j => raw23107 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23107step0 raw23107; decide +kernel
      have hl : raw23107step0Labels = raw23107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23107 raw23107Labels permutation434 hz
    mixedMoment B raw23107step0 raw23107step0Labels = mixedMoment B raw23107step1 raw23107step1Labels := by
      have hz : ∀ j, raw23107step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23107step1 = (fun i j => raw23107step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23107step1 raw23107step0; decide +kernel
      have hl : raw23107step1Labels = raw23107step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23107step0 raw23107step0Labels permutation56 hz
    mixedMoment B raw23107step1 raw23107step1Labels = mixedMoment B raw23107step2 raw23107step2Labels := by
      have ha : raw23107step2 = (fun i j => raw23107step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23107step2 raw23107step1; decide +kernel
      have hl : raw23107step2Labels = raw23107step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23107step1 raw23107step1Labels permutation9 permutation6
    _ = mixedMoment B node1049 node1049Labels := by rfl

def raw23108 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23108Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23108 raw23108Labels = mixedMoment B node973 node973Labels := by
  calc
    mixedMoment B raw23108 raw23108Labels = mixedMoment B raw23108step0 raw23108step0Labels := by
      have ha : raw23108step0 = (fun i j => raw23108 (permutation201 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23108step0 raw23108; decide +kernel
      have hl : raw23108step0Labels = raw23108Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23108 raw23108Labels permutation201 permutation6
    _ = mixedMoment B node973 node973Labels := by rfl

def raw23109 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23109Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23109step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23109step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23109 raw23109Labels = mixedMoment B node1026 node1026Labels := by
  calc
    mixedMoment B raw23109 raw23109Labels = mixedMoment B raw23109step0 raw23109step0Labels := by
      have hz : ∀ j, raw23109 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23109step0 = (fun i j => raw23109 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23109step0 raw23109; decide +kernel
      have hl : raw23109step0Labels = raw23109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23109 raw23109Labels permutation434 hz
    mixedMoment B raw23109step0 raw23109step0Labels = mixedMoment B raw23109step1 raw23109step1Labels := by
      have ha : raw23109step1 = (fun i j => raw23109step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23109step1 raw23109step0; decide +kernel
      have hl : raw23109step1Labels = raw23109step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23109step0 raw23109step0Labels permutation33 permutation6
    _ = mixedMoment B node1026 node1026Labels := by rfl

def raw23110 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23110Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23110step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23110 raw23110Labels = mixedMoment B node1025 node1025Labels := by
  calc
    mixedMoment B raw23110 raw23110Labels = mixedMoment B raw23110step0 raw23110step0Labels := by
      have hz : ∀ j, raw23110 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23110step0 = (fun i j => raw23110 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23110step0 raw23110; decide +kernel
      have hl : raw23110step0Labels = raw23110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23110 raw23110Labels permutation434 hz
    mixedMoment B raw23110step0 raw23110step0Labels = mixedMoment B raw23110step1 raw23110step1Labels := by
      have ha : raw23110step1 = (fun i j => raw23110step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23110step1 raw23110step0; decide +kernel
      have hl : raw23110step1Labels = raw23110step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23110step0 raw23110step0Labels permutation33 permutation6
    _ = mixedMoment B node1025 node1025Labels := by rfl

def raw23111 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23111Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23111step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23111step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23111 raw23111Labels = mixedMoment B node789 node789Labels := by
  calc
    mixedMoment B raw23111 raw23111Labels = mixedMoment B raw23111step0 raw23111step0Labels := by
      have hz : ∀ j, raw23111 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23111step0 = (fun i j => raw23111 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23111step0 raw23111; decide +kernel
      have hl : raw23111step0Labels = raw23111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23111 raw23111Labels permutation346 hz
    mixedMoment B raw23111step0 raw23111step0Labels = mixedMoment B raw23111step1 raw23111step1Labels := by
      have ha : raw23111step1 = (fun i j => raw23111step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23111step1 raw23111step0; decide +kernel
      have hl : raw23111step1Labels = raw23111step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23111step0 raw23111step0Labels permutation33 permutation6
    _ = mixedMoment B node789 node789Labels := by rfl

def raw23112 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23112Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23112step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23112step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23112step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23112step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23112step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23112 raw23112Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw23112 raw23112Labels = mixedMoment B raw23112step0 raw23112step0Labels := by
      have hz : ∀ j, raw23112 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23112step0 = (fun i j => raw23112 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23112step0 raw23112; decide +kernel
      have hl : raw23112step0Labels = raw23112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23112 raw23112Labels permutation346 hz
    mixedMoment B raw23112step0 raw23112step0Labels = mixedMoment B raw23112step1 raw23112step1Labels := by
      have hz : ∀ j, raw23112step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23112step1 = (fun i j => raw23112step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23112step1 raw23112step0; decide +kernel
      have hl : raw23112step1Labels = raw23112step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23112step0 raw23112step0Labels permutation56 hz
    mixedMoment B raw23112step1 raw23112step1Labels = mixedMoment B raw23112step2 raw23112step2Labels := by
      have ha : raw23112step2 = (fun i j => raw23112step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23112step2 raw23112step1; decide +kernel
      have hl : raw23112step2Labels = raw23112step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23112step1 raw23112step1Labels permutation9 permutation6
    _ = mixedMoment B node1049 node1049Labels := by rfl

def raw23113 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23113Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23113step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23113 raw23113Labels = mixedMoment B node973 node973Labels := by
  calc
    mixedMoment B raw23113 raw23113Labels = mixedMoment B raw23113step0 raw23113step0Labels := by
      have ha : raw23113step0 = (fun i j => raw23113 (permutation177 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23113step0 raw23113; decide +kernel
      have hl : raw23113step0Labels = raw23113Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23113 raw23113Labels permutation177 permutation6
    _ = mixedMoment B node973 node973Labels := by rfl

def raw23114 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23114Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23114step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23114step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23114 raw23114Labels = mixedMoment B node1026 node1026Labels := by
  calc
    mixedMoment B raw23114 raw23114Labels = mixedMoment B raw23114step0 raw23114step0Labels := by
      have hz : ∀ j, raw23114 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23114step0 = (fun i j => raw23114 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23114step0 raw23114; decide +kernel
      have hl : raw23114step0Labels = raw23114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23114 raw23114Labels permutation346 hz
    mixedMoment B raw23114step0 raw23114step0Labels = mixedMoment B raw23114step1 raw23114step1Labels := by
      have ha : raw23114step1 = (fun i j => raw23114step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23114step1 raw23114step0; decide +kernel
      have hl : raw23114step1Labels = raw23114step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23114step0 raw23114step0Labels permutation33 permutation6
    _ = mixedMoment B node1026 node1026Labels := by rfl

def raw23115 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23115Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23115step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23115 raw23115Labels = mixedMoment B node1025 node1025Labels := by
  calc
    mixedMoment B raw23115 raw23115Labels = mixedMoment B raw23115step0 raw23115step0Labels := by
      have hz : ∀ j, raw23115 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23115step0 = (fun i j => raw23115 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23115step0 raw23115; decide +kernel
      have hl : raw23115step0Labels = raw23115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23115 raw23115Labels permutation346 hz
    mixedMoment B raw23115step0 raw23115step0Labels = mixedMoment B raw23115step1 raw23115step1Labels := by
      have ha : raw23115step1 = (fun i j => raw23115step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23115step1 raw23115step0; decide +kernel
      have hl : raw23115step1Labels = raw23115step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23115step0 raw23115step0Labels permutation33 permutation6
    _ = mixedMoment B node1025 node1025Labels := by rfl

def raw23116 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23116Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23116step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23116step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23116step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23116step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23116step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23116 raw23116Labels = mixedMoment B node815 node815Labels := by
  calc
    mixedMoment B raw23116 raw23116Labels = mixedMoment B raw23116step0 raw23116step0Labels := by
      have hz : ∀ j, raw23116 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23116step0 = (fun i j => raw23116 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23116step0 raw23116; decide +kernel
      have hl : raw23116step0Labels = raw23116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23116 raw23116Labels permutation434 hz
    mixedMoment B raw23116step0 raw23116step0Labels = mixedMoment B raw23116step1 raw23116step1Labels := by
      have hz : ∀ j, raw23116step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23116step1 = (fun i j => raw23116step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23116step1 raw23116step0; decide +kernel
      have hl : raw23116step1Labels = raw23116step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23116step0 raw23116step0Labels permutation80 hz
    mixedMoment B raw23116step1 raw23116step1Labels = mixedMoment B raw23116step2 raw23116step2Labels := by
      have ha : raw23116step2 = (fun i j => raw23116step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23116step2 raw23116step1; decide +kernel
      have hl : raw23116step2Labels = raw23116step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23116step1 raw23116step1Labels permutation9 permutation6
    _ = mixedMoment B node815 node815Labels := by rfl

def raw23117 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23117Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23117step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23117step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23117step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23117step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -3, 2], ![-2, 0, 2]]
def raw23117step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23117step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![2, -2, 0], ![2, 1, -3]]
def raw23117step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23117 raw23117Labels = mixedMoment B node1094 node1094Labels := by
  calc
    mixedMoment B raw23117 raw23117Labels = mixedMoment B raw23117step0 raw23117step0Labels := by
      have hz : ∀ j, raw23117 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23117step0 = (fun i j => raw23117 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23117step0 raw23117; decide +kernel
      have hl : raw23117step0Labels = raw23117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23117 raw23117Labels permutation434 hz
    mixedMoment B raw23117step0 raw23117step0Labels = mixedMoment B raw23117step1 raw23117step1Labels := by
      have hz : ∀ j, raw23117step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23117step1 = (fun i j => raw23117step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23117step1 raw23117step0; decide +kernel
      have hl : raw23117step1Labels = raw23117step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23117step0 raw23117step0Labels permutation80 hz
    mixedMoment B raw23117step1 raw23117step1Labels = mixedMoment B raw23117step2 raw23117step2Labels := by
      have hz : ∀ j, raw23117step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23117step2 = (fun i j => raw23117step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23117step2 raw23117step1; decide +kernel
      have hl : raw23117step2Labels = raw23117step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23117step1 raw23117step1Labels permutation14 hz
    mixedMoment B raw23117step2 raw23117step2Labels = mixedMoment B raw23117step3 raw23117step3Labels := by
      have ha : raw23117step3 = (fun i j => raw23117step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23117step3 raw23117step2; decide +kernel
      have hl : raw23117step3Labels = raw23117step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23117step2 raw23117step2Labels permutation3 permutation6
    _ = mixedMoment B node1094 node1094Labels := by rfl

def raw23118 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23118Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23118step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23118 raw23118Labels = mixedMoment B node984 node984Labels := by
  calc
    mixedMoment B raw23118 raw23118Labels = mixedMoment B raw23118step0 raw23118step0Labels := by
      have hz : ∀ j, raw23118 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23118step0 = (fun i j => raw23118 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23118step0 raw23118; decide +kernel
      have hl : raw23118step0Labels = raw23118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23118 raw23118Labels permutation434 hz
    mixedMoment B raw23118step0 raw23118step0Labels = mixedMoment B raw23118step1 raw23118step1Labels := by
      have ha : raw23118step1 = (fun i j => raw23118step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23118step1 raw23118step0; decide +kernel
      have hl : raw23118step1Labels = raw23118step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23118step0 raw23118step0Labels permutation39 permutation6
    _ = mixedMoment B node984 node984Labels := by rfl

def raw23119 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23119Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23119step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw23119step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23119 raw23119Labels = mixedMoment B node984 node984Labels := by
  calc
    mixedMoment B raw23119 raw23119Labels = mixedMoment B raw23119step0 raw23119step0Labels := by
      have hz : ∀ j, raw23119 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23119step0 = (fun i j => raw23119 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23119step0 raw23119; decide +kernel
      have hl : raw23119step0Labels = raw23119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23119 raw23119Labels permutation346 hz
    mixedMoment B raw23119step0 raw23119step0Labels = mixedMoment B raw23119step1 raw23119step1Labels := by
      have ha : raw23119step1 = (fun i j => raw23119step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23119step1 raw23119step0; decide +kernel
      have hl : raw23119step1Labels = raw23119step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23119step0 raw23119step0Labels permutation39 permutation6
    _ = mixedMoment B node984 node984Labels := by rfl

def raw23120 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23120Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23120step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23120step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23120step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23120step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw23120step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23120 raw23120Labels = mixedMoment B node1048 node1048Labels := by
  calc
    mixedMoment B raw23120 raw23120Labels = mixedMoment B raw23120step0 raw23120step0Labels := by
      have hz : ∀ j, raw23120 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23120step0 = (fun i j => raw23120 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23120step0 raw23120; decide +kernel
      have hl : raw23120step0Labels = raw23120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23120 raw23120Labels permutation434 hz
    mixedMoment B raw23120step0 raw23120step0Labels = mixedMoment B raw23120step1 raw23120step1Labels := by
      have hz : ∀ j, raw23120step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23120step1 = (fun i j => raw23120step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23120step1 raw23120step0; decide +kernel
      have hl : raw23120step1Labels = raw23120step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23120step0 raw23120step0Labels permutation80 hz
    mixedMoment B raw23120step1 raw23120step1Labels = mixedMoment B raw23120step2 raw23120step2Labels := by
      have ha : raw23120step2 = (fun i j => raw23120step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23120step2 raw23120step1; decide +kernel
      have hl : raw23120step2Labels = raw23120step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23120step1 raw23120step1Labels permutation9 permutation6
    _ = mixedMoment B node1048 node1048Labels := by rfl

def raw23121 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23121Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23121step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23121step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23121step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23121step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23121step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23121 raw23121Labels = mixedMoment B node816 node816Labels := by
  calc
    mixedMoment B raw23121 raw23121Labels = mixedMoment B raw23121step0 raw23121step0Labels := by
      have hz : ∀ j, raw23121 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23121step0 = (fun i j => raw23121 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23121step0 raw23121; decide +kernel
      have hl : raw23121step0Labels = raw23121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23121 raw23121Labels permutation434 hz
    mixedMoment B raw23121step0 raw23121step0Labels = mixedMoment B raw23121step1 raw23121step1Labels := by
      have hz : ∀ j, raw23121step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23121step1 = (fun i j => raw23121step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23121step1 raw23121step0; decide +kernel
      have hl : raw23121step1Labels = raw23121step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23121step0 raw23121step0Labels permutation80 hz
    mixedMoment B raw23121step1 raw23121step1Labels = mixedMoment B raw23121step2 raw23121step2Labels := by
      have ha : raw23121step2 = (fun i j => raw23121step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23121step2 raw23121step1; decide +kernel
      have hl : raw23121step2Labels = raw23121step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23121step1 raw23121step1Labels permutation9 permutation6
    _ = mixedMoment B node816 node816Labels := by rfl

def raw23122 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23122Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23122step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw23122step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23122 raw23122Labels = mixedMoment B node985 node985Labels := by
  calc
    mixedMoment B raw23122 raw23122Labels = mixedMoment B raw23122step0 raw23122step0Labels := by
      have hz : ∀ j, raw23122 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23122step0 = (fun i j => raw23122 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23122step0 raw23122; decide +kernel
      have hl : raw23122step0Labels = raw23122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23122 raw23122Labels permutation434 hz
    mixedMoment B raw23122step0 raw23122step0Labels = mixedMoment B raw23122step1 raw23122step1Labels := by
      have ha : raw23122step1 = (fun i j => raw23122step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw23122step1 raw23122step0; decide +kernel
      have hl : raw23122step1Labels = raw23122step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23122step0 raw23122step0Labels permutation39 permutation6
    _ = mixedMoment B node985 node985Labels := by rfl

def raw23123 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23123Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23123step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23123step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23123step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23123 raw23123Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw23123 raw23123Labels = mixedMoment B raw23123step0 raw23123step0Labels := by
      have hz : ∀ j, raw23123 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23123step0 = (fun i j => raw23123 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23123step0 raw23123; decide +kernel
      have hl : raw23123step0Labels = raw23123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23123 raw23123Labels permutation434 hz
    mixedMoment B raw23123step0 raw23123step0Labels = mixedMoment B raw23123step1 raw23123step1Labels := by
      have ha : raw23123step1 = (fun i j => raw23123step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23123step1 raw23123step0; decide +kernel
      have hl : raw23123step1Labels = raw23123step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23123step0 raw23123step0Labels permutation32 permutation7
    mixedMoment B raw23123step1 raw23123step1Labels = mixedMoment B raw23123step2 raw23123step2Labels := by
      have ha : raw23123step2 = raw23123step1 := by apply Matrix.ext; unfold raw23123step2 raw23123step1; decide +kernel
      have hl : raw23123step1Labels = labelEmbedding1 ∘ raw23123step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23123step1 raw23123step1Labels raw23123step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1219 node1219Labels := by rfl

def raw23124 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23124Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23124step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23124step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23124step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23124step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23124step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23124step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23124step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23124 raw23124Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw23124 raw23124Labels = mixedMoment B raw23124step0 raw23124step0Labels := by
      have hz : ∀ j, raw23124 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23124step0 = (fun i j => raw23124 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23124step0 raw23124; decide +kernel
      have hl : raw23124step0Labels = raw23124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23124 raw23124Labels permutation434 hz
    mixedMoment B raw23124step0 raw23124step0Labels = mixedMoment B raw23124step1 raw23124step1Labels := by
      have hz : ∀ j, raw23124step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23124step1 = (fun i j => raw23124step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23124step1 raw23124step0; decide +kernel
      have hl : raw23124step1Labels = raw23124step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23124step0 raw23124step0Labels permutation80 hz
    mixedMoment B raw23124step1 raw23124step1Labels = mixedMoment B raw23124step2 raw23124step2Labels := by
      have ha : raw23124step2 = (fun i j => raw23124step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23124step2 raw23124step1; decide +kernel
      have hl : raw23124step2Labels = raw23124step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23124step1 raw23124step1Labels permutation8 permutation7
    mixedMoment B raw23124step2 raw23124step2Labels = mixedMoment B raw23124step3 raw23124step3Labels := by
      have ha : raw23124step3 = raw23124step2 := by apply Matrix.ext; unfold raw23124step3 raw23124step2; decide +kernel
      have hl : raw23124step2Labels = labelEmbedding1 ∘ raw23124step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23124step2 raw23124step2Labels raw23124step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1246 node1246Labels := by rfl

def raw23125 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23125Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23125step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23125step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23125step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23125step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23125step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw23125step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23125step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw23125step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23125 raw23125Labels = mixedMoment B node1245 node1245Labels := by
  calc
    mixedMoment B raw23125 raw23125Labels = mixedMoment B raw23125step0 raw23125step0Labels := by
      have hz : ∀ j, raw23125 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23125step0 = (fun i j => raw23125 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23125step0 raw23125; decide +kernel
      have hl : raw23125step0Labels = raw23125Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23125 raw23125Labels permutation434 hz
    mixedMoment B raw23125step0 raw23125step0Labels = mixedMoment B raw23125step1 raw23125step1Labels := by
      have hz : ∀ j, raw23125step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23125step1 = (fun i j => raw23125step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23125step1 raw23125step0; decide +kernel
      have hl : raw23125step1Labels = raw23125step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23125step0 raw23125step0Labels permutation80 hz
    mixedMoment B raw23125step1 raw23125step1Labels = mixedMoment B raw23125step2 raw23125step2Labels := by
      have ha : raw23125step2 = (fun i j => raw23125step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23125step2 raw23125step1; decide +kernel
      have hl : raw23125step2Labels = raw23125step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23125step1 raw23125step1Labels permutation8 permutation7
    mixedMoment B raw23125step2 raw23125step2Labels = mixedMoment B raw23125step3 raw23125step3Labels := by
      have ha : raw23125step3 = raw23125step2 := by apply Matrix.ext; unfold raw23125step3 raw23125step2; decide +kernel
      have hl : raw23125step2Labels = labelEmbedding1 ∘ raw23125step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23125step2 raw23125step2Labels raw23125step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1245 node1245Labels := by rfl

def raw23126 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23126Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23126step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23126step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23126step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23126step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -4, 0], ![0, 2, -2], ![-2, 2, 0], ![-2, 0, 2]]
def raw23126step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23126step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw23126step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23126step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw23126step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23126 raw23126Labels = mixedMoment B node1472 node1472Labels := by
  calc
    mixedMoment B raw23126 raw23126Labels = mixedMoment B raw23126step0 raw23126step0Labels := by
      have hz : ∀ j, raw23126 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23126step0 = (fun i j => raw23126 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23126step0 raw23126; decide +kernel
      have hl : raw23126step0Labels = raw23126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23126 raw23126Labels permutation434 hz
    mixedMoment B raw23126step0 raw23126step0Labels = mixedMoment B raw23126step1 raw23126step1Labels := by
      have hz : ∀ j, raw23126step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23126step1 = (fun i j => raw23126step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23126step1 raw23126step0; decide +kernel
      have hl : raw23126step1Labels = raw23126step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23126step0 raw23126step0Labels permutation80 hz
    mixedMoment B raw23126step1 raw23126step1Labels = mixedMoment B raw23126step2 raw23126step2Labels := by
      have ha : raw23126step2 = (fun i j => raw23126step1 (permutation13 i) (permutation5 j)) := by apply Matrix.ext; unfold raw23126step2 raw23126step1; decide +kernel
      have hl : raw23126step2Labels = raw23126step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23126step1 raw23126step1Labels permutation13 permutation5
    mixedMoment B raw23126step2 raw23126step2Labels = mixedMoment B raw23126step3 raw23126step3Labels := by
      have ha : raw23126step3 = -raw23126step2 := by apply Matrix.ext; change ∀ i j, raw23126step3 i j = -(raw23126step2 i j); unfold raw23126step3 raw23126step2; decide +kernel
      have hl : raw23126step3Labels = raw23126step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23126step3 raw23126step3Labels = mixedMoment B raw23126step4 raw23126step4Labels := by
      have ha : raw23126step4 = raw23126step3 := by apply Matrix.ext; unfold raw23126step4 raw23126step3; decide +kernel
      have hl : raw23126step3Labels = labelEmbedding1 ∘ raw23126step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23126step3 raw23126step3Labels raw23126step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1472 node1472Labels := by rfl

def raw23127 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23127Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23127step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23127step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23127step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23127 raw23127Labels = mixedMoment B node1362 node1362Labels := by
  calc
    mixedMoment B raw23127 raw23127Labels = mixedMoment B raw23127step0 raw23127step0Labels := by
      have hz : ∀ j, raw23127 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23127step0 = (fun i j => raw23127 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23127step0 raw23127; decide +kernel
      have hl : raw23127step0Labels = raw23127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23127 raw23127Labels permutation434 hz
    mixedMoment B raw23127step0 raw23127step0Labels = mixedMoment B raw23127step1 raw23127step1Labels := by
      have ha : raw23127step1 = (fun i j => raw23127step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23127step1 raw23127step0; decide +kernel
      have hl : raw23127step1Labels = raw23127step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23127step0 raw23127step0Labels permutation32 permutation7
    mixedMoment B raw23127step1 raw23127step1Labels = mixedMoment B raw23127step2 raw23127step2Labels := by
      have ha : raw23127step2 = raw23127step1 := by apply Matrix.ext; unfold raw23127step2 raw23127step1; decide +kernel
      have hl : raw23127step1Labels = labelEmbedding1 ∘ raw23127step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23127step1 raw23127step1Labels raw23127step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1362 node1362Labels := by rfl

def raw23128 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23128Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23128step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23128step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23128step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23128 raw23128Labels = mixedMoment B node1362 node1362Labels := by
  calc
    mixedMoment B raw23128 raw23128Labels = mixedMoment B raw23128step0 raw23128step0Labels := by
      have hz : ∀ j, raw23128 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23128step0 = (fun i j => raw23128 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23128step0 raw23128; decide +kernel
      have hl : raw23128step0Labels = raw23128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23128 raw23128Labels permutation346 hz
    mixedMoment B raw23128step0 raw23128step0Labels = mixedMoment B raw23128step1 raw23128step1Labels := by
      have ha : raw23128step1 = (fun i j => raw23128step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23128step1 raw23128step0; decide +kernel
      have hl : raw23128step1Labels = raw23128step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23128step0 raw23128step0Labels permutation32 permutation7
    mixedMoment B raw23128step1 raw23128step1Labels = mixedMoment B raw23128step2 raw23128step2Labels := by
      have ha : raw23128step2 = raw23128step1 := by apply Matrix.ext; unfold raw23128step2 raw23128step1; decide +kernel
      have hl : raw23128step1Labels = labelEmbedding1 ∘ raw23128step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23128step1 raw23128step1Labels raw23128step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1362 node1362Labels := by rfl

def raw23129 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23129Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23129step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23129step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23129step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23129step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw23129step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23129step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw23129step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23129 raw23129Labels = mixedMoment B node1375 node1375Labels := by
  calc
    mixedMoment B raw23129 raw23129Labels = mixedMoment B raw23129step0 raw23129step0Labels := by
      have hz : ∀ j, raw23129 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23129step0 = (fun i j => raw23129 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23129step0 raw23129; decide +kernel
      have hl : raw23129step0Labels = raw23129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23129 raw23129Labels permutation434 hz
    mixedMoment B raw23129step0 raw23129step0Labels = mixedMoment B raw23129step1 raw23129step1Labels := by
      have hz : ∀ j, raw23129step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23129step1 = (fun i j => raw23129step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23129step1 raw23129step0; decide +kernel
      have hl : raw23129step1Labels = raw23129step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23129step0 raw23129step0Labels permutation80 hz
    mixedMoment B raw23129step1 raw23129step1Labels = mixedMoment B raw23129step2 raw23129step2Labels := by
      have ha : raw23129step2 = (fun i j => raw23129step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23129step2 raw23129step1; decide +kernel
      have hl : raw23129step2Labels = raw23129step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23129step1 raw23129step1Labels permutation8 permutation7
    mixedMoment B raw23129step2 raw23129step2Labels = mixedMoment B raw23129step3 raw23129step3Labels := by
      have ha : raw23129step3 = raw23129step2 := by apply Matrix.ext; unfold raw23129step3 raw23129step2; decide +kernel
      have hl : raw23129step2Labels = labelEmbedding1 ∘ raw23129step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23129step2 raw23129step2Labels raw23129step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1375 node1375Labels := by rfl

def raw23130 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23130Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23130step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23130step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![2, -2, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23130step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23130step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -2, 0], ![2, 1, -3]]
def raw23130step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23130step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![2, -2, 0], ![2, 1, -3]]
def raw23130step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23130 raw23130Labels = mixedMoment B node1374 node1374Labels := by
  calc
    mixedMoment B raw23130 raw23130Labels = mixedMoment B raw23130step0 raw23130step0Labels := by
      have hz : ∀ j, raw23130 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23130step0 = (fun i j => raw23130 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23130step0 raw23130; decide +kernel
      have hl : raw23130step0Labels = raw23130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23130 raw23130Labels permutation434 hz
    mixedMoment B raw23130step0 raw23130step0Labels = mixedMoment B raw23130step1 raw23130step1Labels := by
      have hz : ∀ j, raw23130step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23130step1 = (fun i j => raw23130step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23130step1 raw23130step0; decide +kernel
      have hl : raw23130step1Labels = raw23130step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23130step0 raw23130step0Labels permutation80 hz
    mixedMoment B raw23130step1 raw23130step1Labels = mixedMoment B raw23130step2 raw23130step2Labels := by
      have ha : raw23130step2 = (fun i j => raw23130step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23130step2 raw23130step1; decide +kernel
      have hl : raw23130step2Labels = raw23130step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23130step1 raw23130step1Labels permutation8 permutation7
    mixedMoment B raw23130step2 raw23130step2Labels = mixedMoment B raw23130step3 raw23130step3Labels := by
      have ha : raw23130step3 = raw23130step2 := by apply Matrix.ext; unfold raw23130step3 raw23130step2; decide +kernel
      have hl : raw23130step2Labels = labelEmbedding1 ∘ raw23130step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23130step2 raw23130step2Labels raw23130step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1374 node1374Labels := by rfl

def raw23131 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23131Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23131step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23131step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -4, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw23131step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23131step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw23131step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23131step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw23131step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23131 raw23131Labels = mixedMoment B node1470 node1470Labels := by
  calc
    mixedMoment B raw23131 raw23131Labels = mixedMoment B raw23131step0 raw23131step0Labels := by
      have hz : ∀ j, raw23131 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23131step0 = (fun i j => raw23131 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23131step0 raw23131; decide +kernel
      have hl : raw23131step0Labels = raw23131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23131 raw23131Labels permutation434 hz
    mixedMoment B raw23131step0 raw23131step0Labels = mixedMoment B raw23131step1 raw23131step1Labels := by
      have ha : raw23131step1 = (fun i j => raw23131step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw23131step1 raw23131step0; decide +kernel
      have hl : raw23131step1Labels = raw23131step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23131step0 raw23131step0Labels permutation50 permutation5
    mixedMoment B raw23131step1 raw23131step1Labels = mixedMoment B raw23131step2 raw23131step2Labels := by
      have ha : raw23131step2 = -raw23131step1 := by apply Matrix.ext; change ∀ i j, raw23131step2 i j = -(raw23131step1 i j); unfold raw23131step2 raw23131step1; decide +kernel
      have hl : raw23131step2Labels = raw23131step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23131step2 raw23131step2Labels = mixedMoment B raw23131step3 raw23131step3Labels := by
      have ha : raw23131step3 = raw23131step2 := by apply Matrix.ext; unfold raw23131step3 raw23131step2; decide +kernel
      have hl : raw23131step2Labels = labelEmbedding1 ∘ raw23131step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23131step2 raw23131step2Labels raw23131step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1470 node1470Labels := by rfl

def raw23132 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23132Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23132step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23132step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23132step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23132step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23132step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23132step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23132step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23132 raw23132Labels = mixedMoment B node1419 node1419Labels := by
  calc
    mixedMoment B raw23132 raw23132Labels = mixedMoment B raw23132step0 raw23132step0Labels := by
      have hz : ∀ j, raw23132 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23132step0 = (fun i j => raw23132 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23132step0 raw23132; decide +kernel
      have hl : raw23132step0Labels = raw23132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23132 raw23132Labels permutation434 hz
    mixedMoment B raw23132step0 raw23132step0Labels = mixedMoment B raw23132step1 raw23132step1Labels := by
      have hz : ∀ j, raw23132step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23132step1 = (fun i j => raw23132step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23132step1 raw23132step0; decide +kernel
      have hl : raw23132step1Labels = raw23132step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23132step0 raw23132step0Labels permutation56 hz
    mixedMoment B raw23132step1 raw23132step1Labels = mixedMoment B raw23132step2 raw23132step2Labels := by
      have ha : raw23132step2 = (fun i j => raw23132step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23132step2 raw23132step1; decide +kernel
      have hl : raw23132step2Labels = raw23132step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23132step1 raw23132step1Labels permutation8 permutation7
    mixedMoment B raw23132step2 raw23132step2Labels = mixedMoment B raw23132step3 raw23132step3Labels := by
      have ha : raw23132step3 = raw23132step2 := by apply Matrix.ext; unfold raw23132step3 raw23132step2; decide +kernel
      have hl : raw23132step2Labels = labelEmbedding1 ∘ raw23132step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23132step2 raw23132step2Labels raw23132step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1419 node1419Labels := by rfl

def raw23133 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23133Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23133step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23133step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23133 raw23133Labels = mixedMoment B node1380 node1380Labels := by
  calc
    mixedMoment B raw23133 raw23133Labels = mixedMoment B raw23133step0 raw23133step0Labels := by
      have ha : raw23133step0 = (fun i j => raw23133 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23133step0 raw23133; decide +kernel
      have hl : raw23133step0Labels = raw23133Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23133 raw23133Labels permutation152 permutation7
    mixedMoment B raw23133step0 raw23133step0Labels = mixedMoment B raw23133step1 raw23133step1Labels := by
      have ha : raw23133step1 = raw23133step0 := by apply Matrix.ext; unfold raw23133step1 raw23133step0; decide +kernel
      have hl : raw23133step0Labels = labelEmbedding1 ∘ raw23133step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23133step0 raw23133step0Labels raw23133step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1380 node1380Labels := by rfl

def raw23134 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23134Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23134step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23134step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23134step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23134step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23134step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23134 raw23134Labels = mixedMoment B node1391 node1391Labels := by
  calc
    mixedMoment B raw23134 raw23134Labels = mixedMoment B raw23134step0 raw23134step0Labels := by
      have hz : ∀ j, raw23134 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23134step0 = (fun i j => raw23134 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23134step0 raw23134; decide +kernel
      have hl : raw23134step0Labels = raw23134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23134 raw23134Labels permutation434 hz
    mixedMoment B raw23134step0 raw23134step0Labels = mixedMoment B raw23134step1 raw23134step1Labels := by
      have ha : raw23134step1 = (fun i j => raw23134step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23134step1 raw23134step0; decide +kernel
      have hl : raw23134step1Labels = raw23134step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23134step0 raw23134step0Labels permutation32 permutation7
    mixedMoment B raw23134step1 raw23134step1Labels = mixedMoment B raw23134step2 raw23134step2Labels := by
      have ha : raw23134step2 = raw23134step1 := by apply Matrix.ext; unfold raw23134step2 raw23134step1; decide +kernel
      have hl : raw23134step1Labels = labelEmbedding1 ∘ raw23134step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23134step1 raw23134step1Labels raw23134step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1391 node1391Labels := by rfl

def raw23135 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23135Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23135step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw23135step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23135step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw23135step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23135 raw23135Labels = mixedMoment B node1390 node1390Labels := by
  calc
    mixedMoment B raw23135 raw23135Labels = mixedMoment B raw23135step0 raw23135step0Labels := by
      have hz : ∀ j, raw23135 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23135step0 = (fun i j => raw23135 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23135step0 raw23135; decide +kernel
      have hl : raw23135step0Labels = raw23135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23135 raw23135Labels permutation434 hz
    mixedMoment B raw23135step0 raw23135step0Labels = mixedMoment B raw23135step1 raw23135step1Labels := by
      have ha : raw23135step1 = (fun i j => raw23135step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23135step1 raw23135step0; decide +kernel
      have hl : raw23135step1Labels = raw23135step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23135step0 raw23135step0Labels permutation32 permutation7
    mixedMoment B raw23135step1 raw23135step1Labels = mixedMoment B raw23135step2 raw23135step2Labels := by
      have ha : raw23135step2 = raw23135step1 := by apply Matrix.ext; unfold raw23135step2 raw23135step1; decide +kernel
      have hl : raw23135step1Labels = labelEmbedding1 ∘ raw23135step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23135step1 raw23135step1Labels raw23135step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1390 node1390Labels := by rfl

def raw23136 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23136Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23136step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23136step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -4, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw23136step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23136step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw23136step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23136step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw23136step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23136 raw23136Labels = mixedMoment B node1470 node1470Labels := by
  calc
    mixedMoment B raw23136 raw23136Labels = mixedMoment B raw23136step0 raw23136step0Labels := by
      have hz : ∀ j, raw23136 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23136step0 = (fun i j => raw23136 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23136step0 raw23136; decide +kernel
      have hl : raw23136step0Labels = raw23136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23136 raw23136Labels permutation346 hz
    mixedMoment B raw23136step0 raw23136step0Labels = mixedMoment B raw23136step1 raw23136step1Labels := by
      have ha : raw23136step1 = (fun i j => raw23136step0 (permutation50 i) (permutation5 j)) := by apply Matrix.ext; unfold raw23136step1 raw23136step0; decide +kernel
      have hl : raw23136step1Labels = raw23136step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23136step0 raw23136step0Labels permutation50 permutation5
    mixedMoment B raw23136step1 raw23136step1Labels = mixedMoment B raw23136step2 raw23136step2Labels := by
      have ha : raw23136step2 = -raw23136step1 := by apply Matrix.ext; change ∀ i j, raw23136step2 i j = -(raw23136step1 i j); unfold raw23136step2 raw23136step1; decide +kernel
      have hl : raw23136step2Labels = raw23136step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23136step2 raw23136step2Labels = mixedMoment B raw23136step3 raw23136step3Labels := by
      have ha : raw23136step3 = raw23136step2 := by apply Matrix.ext; unfold raw23136step3 raw23136step2; decide +kernel
      have hl : raw23136step2Labels = labelEmbedding1 ∘ raw23136step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23136step2 raw23136step2Labels raw23136step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1470 node1470Labels := by rfl

def raw23137 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23137Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23137step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23137step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23137step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23137step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23137step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23137step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw23137step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23137 raw23137Labels = mixedMoment B node1419 node1419Labels := by
  calc
    mixedMoment B raw23137 raw23137Labels = mixedMoment B raw23137step0 raw23137step0Labels := by
      have hz : ∀ j, raw23137 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23137step0 = (fun i j => raw23137 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23137step0 raw23137; decide +kernel
      have hl : raw23137step0Labels = raw23137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23137 raw23137Labels permutation346 hz
    mixedMoment B raw23137step0 raw23137step0Labels = mixedMoment B raw23137step1 raw23137step1Labels := by
      have hz : ∀ j, raw23137step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw23137step1 = (fun i j => raw23137step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw23137step1 raw23137step0; decide +kernel
      have hl : raw23137step1Labels = raw23137step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23137step0 raw23137step0Labels permutation56 hz
    mixedMoment B raw23137step1 raw23137step1Labels = mixedMoment B raw23137step2 raw23137step2Labels := by
      have ha : raw23137step2 = (fun i j => raw23137step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23137step2 raw23137step1; decide +kernel
      have hl : raw23137step2Labels = raw23137step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23137step1 raw23137step1Labels permutation8 permutation7
    mixedMoment B raw23137step2 raw23137step2Labels = mixedMoment B raw23137step3 raw23137step3Labels := by
      have ha : raw23137step3 = raw23137step2 := by apply Matrix.ext; unfold raw23137step3 raw23137step2; decide +kernel
      have hl : raw23137step2Labels = labelEmbedding1 ∘ raw23137step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23137step2 raw23137step2Labels raw23137step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1419 node1419Labels := by rfl

def raw23138 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw23138Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23138step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23138step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw23138step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23138 raw23138Labels = mixedMoment B node1380 node1380Labels := by
  calc
    mixedMoment B raw23138 raw23138Labels = mixedMoment B raw23138step0 raw23138step0Labels := by
      have ha : raw23138step0 = (fun i j => raw23138 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23138step0 raw23138; decide +kernel
      have hl : raw23138step0Labels = raw23138Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23138 raw23138Labels permutation158 permutation7
    mixedMoment B raw23138step0 raw23138step0Labels = mixedMoment B raw23138step1 raw23138step1Labels := by
      have ha : raw23138step1 = raw23138step0 := by apply Matrix.ext; unfold raw23138step1 raw23138step0; decide +kernel
      have hl : raw23138step0Labels = labelEmbedding1 ∘ raw23138step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23138step0 raw23138step0Labels raw23138step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1380 node1380Labels := by rfl

def raw23139 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23139Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw23139step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23139step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw23139step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23139 raw23139Labels = mixedMoment B node1391 node1391Labels := by
  calc
    mixedMoment B raw23139 raw23139Labels = mixedMoment B raw23139step0 raw23139step0Labels := by
      have hz : ∀ j, raw23139 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23139step0 = (fun i j => raw23139 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23139step0 raw23139; decide +kernel
      have hl : raw23139step0Labels = raw23139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23139 raw23139Labels permutation346 hz
    mixedMoment B raw23139step0 raw23139step0Labels = mixedMoment B raw23139step1 raw23139step1Labels := by
      have ha : raw23139step1 = (fun i j => raw23139step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23139step1 raw23139step0; decide +kernel
      have hl : raw23139step1Labels = raw23139step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23139step0 raw23139step0Labels permutation32 permutation7
    mixedMoment B raw23139step1 raw23139step1Labels = mixedMoment B raw23139step2 raw23139step2Labels := by
      have ha : raw23139step2 = raw23139step1 := by apply Matrix.ext; unfold raw23139step2 raw23139step1; decide +kernel
      have hl : raw23139step1Labels = labelEmbedding1 ∘ raw23139step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23139step1 raw23139step1Labels raw23139step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1391 node1391Labels := by rfl

def raw23140 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23140Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw23140step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw23140step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw23140step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23140 raw23140Labels = mixedMoment B node1390 node1390Labels := by
  calc
    mixedMoment B raw23140 raw23140Labels = mixedMoment B raw23140step0 raw23140step0Labels := by
      have hz : ∀ j, raw23140 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23140step0 = (fun i j => raw23140 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23140step0 raw23140; decide +kernel
      have hl : raw23140step0Labels = raw23140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23140 raw23140Labels permutation346 hz
    mixedMoment B raw23140step0 raw23140step0Labels = mixedMoment B raw23140step1 raw23140step1Labels := by
      have ha : raw23140step1 = (fun i j => raw23140step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23140step1 raw23140step0; decide +kernel
      have hl : raw23140step1Labels = raw23140step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23140step0 raw23140step0Labels permutation32 permutation7
    mixedMoment B raw23140step1 raw23140step1Labels = mixedMoment B raw23140step2 raw23140step2Labels := by
      have ha : raw23140step2 = raw23140step1 := by apply Matrix.ext; unfold raw23140step2 raw23140step1; decide +kernel
      have hl : raw23140step1Labels = labelEmbedding1 ∘ raw23140step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23140step1 raw23140step1Labels raw23140step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1390 node1390Labels := by rfl

def raw23141 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23141Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23141step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23141step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23141step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23141step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -4, 0], ![0, 2, -2], ![-1, 0, 1], ![-3, 2, 1]]
def raw23141step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23141step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw23141step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23141step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw23141step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23141 raw23141Labels = mixedMoment B node1471 node1471Labels := by
  calc
    mixedMoment B raw23141 raw23141Labels = mixedMoment B raw23141step0 raw23141step0Labels := by
      have hz : ∀ j, raw23141 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23141step0 = (fun i j => raw23141 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23141step0 raw23141; decide +kernel
      have hl : raw23141step0Labels = raw23141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23141 raw23141Labels permutation434 hz
    mixedMoment B raw23141step0 raw23141step0Labels = mixedMoment B raw23141step1 raw23141step1Labels := by
      have hz : ∀ j, raw23141step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23141step1 = (fun i j => raw23141step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23141step1 raw23141step0; decide +kernel
      have hl : raw23141step1Labels = raw23141step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23141step0 raw23141step0Labels permutation80 hz
    mixedMoment B raw23141step1 raw23141step1Labels = mixedMoment B raw23141step2 raw23141step2Labels := by
      have ha : raw23141step2 = (fun i j => raw23141step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw23141step2 raw23141step1; decide +kernel
      have hl : raw23141step2Labels = raw23141step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23141step1 raw23141step1Labels permutation12 permutation5
    mixedMoment B raw23141step2 raw23141step2Labels = mixedMoment B raw23141step3 raw23141step3Labels := by
      have ha : raw23141step3 = -raw23141step2 := by apply Matrix.ext; change ∀ i j, raw23141step3 i j = -(raw23141step2 i j); unfold raw23141step3 raw23141step2; decide +kernel
      have hl : raw23141step3Labels = raw23141step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw23141step3 raw23141step3Labels = mixedMoment B raw23141step4 raw23141step4Labels := by
      have ha : raw23141step4 = raw23141step3 := by apply Matrix.ext; unfold raw23141step4 raw23141step3; decide +kernel
      have hl : raw23141step3Labels = labelEmbedding1 ∘ raw23141step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23141step3 raw23141step3Labels raw23141step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1471 node1471Labels := by rfl

def raw23142 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23142Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23142step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23142step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23142step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23142step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![1, -3, 2], ![-2, 0, 2]]
def raw23142step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23142step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw23142step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23142step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![2, -3, 1], ![2, 0, -2]]
def raw23142step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23142 raw23142Labels = mixedMoment B node1454 node1454Labels := by
  calc
    mixedMoment B raw23142 raw23142Labels = mixedMoment B raw23142step0 raw23142step0Labels := by
      have hz : ∀ j, raw23142 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23142step0 = (fun i j => raw23142 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23142step0 raw23142; decide +kernel
      have hl : raw23142step0Labels = raw23142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23142 raw23142Labels permutation434 hz
    mixedMoment B raw23142step0 raw23142step0Labels = mixedMoment B raw23142step1 raw23142step1Labels := by
      have hz : ∀ j, raw23142step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23142step1 = (fun i j => raw23142step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23142step1 raw23142step0; decide +kernel
      have hl : raw23142step1Labels = raw23142step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23142step0 raw23142step0Labels permutation80 hz
    mixedMoment B raw23142step1 raw23142step1Labels = mixedMoment B raw23142step2 raw23142step2Labels := by
      have hz : ∀ j, raw23142step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw23142step2 = (fun i j => raw23142step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw23142step2 raw23142step1; decide +kernel
      have hl : raw23142step2Labels = raw23142step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23142step1 raw23142step1Labels permutation14 hz
    mixedMoment B raw23142step2 raw23142step2Labels = mixedMoment B raw23142step3 raw23142step3Labels := by
      have ha : raw23142step3 = (fun i j => raw23142step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23142step3 raw23142step2; decide +kernel
      have hl : raw23142step3Labels = raw23142step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23142step2 raw23142step2Labels permutation2 permutation7
    mixedMoment B raw23142step3 raw23142step3Labels = mixedMoment B raw23142step4 raw23142step4Labels := by
      have ha : raw23142step4 = raw23142step3 := by apply Matrix.ext; unfold raw23142step4 raw23142step3; decide +kernel
      have hl : raw23142step3Labels = labelEmbedding1 ∘ raw23142step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23142step3 raw23142step3Labels raw23142step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1454 node1454Labels := by rfl

def raw23143 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23143Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23143step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23143step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23143step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23143 raw23143Labels = mixedMoment B node1400 node1400Labels := by
  calc
    mixedMoment B raw23143 raw23143Labels = mixedMoment B raw23143step0 raw23143step0Labels := by
      have hz : ∀ j, raw23143 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23143step0 = (fun i j => raw23143 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23143step0 raw23143; decide +kernel
      have hl : raw23143step0Labels = raw23143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23143 raw23143Labels permutation434 hz
    mixedMoment B raw23143step0 raw23143step0Labels = mixedMoment B raw23143step1 raw23143step1Labels := by
      have ha : raw23143step1 = (fun i j => raw23143step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23143step1 raw23143step0; decide +kernel
      have hl : raw23143step1Labels = raw23143step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23143step0 raw23143step0Labels permutation32 permutation7
    mixedMoment B raw23143step1 raw23143step1Labels = mixedMoment B raw23143step2 raw23143step2Labels := by
      have ha : raw23143step2 = raw23143step1 := by apply Matrix.ext; unfold raw23143step2 raw23143step1; decide +kernel
      have hl : raw23143step1Labels = labelEmbedding1 ∘ raw23143step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23143step1 raw23143step1Labels raw23143step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1400 node1400Labels := by rfl

def raw23144 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23144Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw23144step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23144step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw23144step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23144 raw23144Labels = mixedMoment B node1400 node1400Labels := by
  calc
    mixedMoment B raw23144 raw23144Labels = mixedMoment B raw23144step0 raw23144step0Labels := by
      have hz : ∀ j, raw23144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23144step0 = (fun i j => raw23144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23144step0 raw23144; decide +kernel
      have hl : raw23144step0Labels = raw23144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23144 raw23144Labels permutation346 hz
    mixedMoment B raw23144step0 raw23144step0Labels = mixedMoment B raw23144step1 raw23144step1Labels := by
      have ha : raw23144step1 = (fun i j => raw23144step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23144step1 raw23144step0; decide +kernel
      have hl : raw23144step1Labels = raw23144step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23144step0 raw23144step0Labels permutation32 permutation7
    mixedMoment B raw23144step1 raw23144step1Labels = mixedMoment B raw23144step2 raw23144step2Labels := by
      have ha : raw23144step2 = raw23144step1 := by apply Matrix.ext; unfold raw23144step2 raw23144step1; decide +kernel
      have hl : raw23144step1Labels = labelEmbedding1 ∘ raw23144step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23144step1 raw23144step1Labels raw23144step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1400 node1400Labels := by rfl

def raw23145 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23145Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23145step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23145step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw23145step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23145step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw23145step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23145step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -3, 1], ![2, 1, -3]]
def raw23145step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23145 raw23145Labels = mixedMoment B node1418 node1418Labels := by
  calc
    mixedMoment B raw23145 raw23145Labels = mixedMoment B raw23145step0 raw23145step0Labels := by
      have hz : ∀ j, raw23145 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23145step0 = (fun i j => raw23145 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23145step0 raw23145; decide +kernel
      have hl : raw23145step0Labels = raw23145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23145 raw23145Labels permutation434 hz
    mixedMoment B raw23145step0 raw23145step0Labels = mixedMoment B raw23145step1 raw23145step1Labels := by
      have hz : ∀ j, raw23145step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23145step1 = (fun i j => raw23145step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23145step1 raw23145step0; decide +kernel
      have hl : raw23145step1Labels = raw23145step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23145step0 raw23145step0Labels permutation80 hz
    mixedMoment B raw23145step1 raw23145step1Labels = mixedMoment B raw23145step2 raw23145step2Labels := by
      have ha : raw23145step2 = (fun i j => raw23145step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23145step2 raw23145step1; decide +kernel
      have hl : raw23145step2Labels = raw23145step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23145step1 raw23145step1Labels permutation8 permutation7
    mixedMoment B raw23145step2 raw23145step2Labels = mixedMoment B raw23145step3 raw23145step3Labels := by
      have ha : raw23145step3 = raw23145step2 := by apply Matrix.ext; unfold raw23145step3 raw23145step2; decide +kernel
      have hl : raw23145step2Labels = labelEmbedding1 ∘ raw23145step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23145step2 raw23145step2Labels raw23145step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1418 node1418Labels := by rfl

def raw23146 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23146Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23146step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23146step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23146step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23146step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw23146step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23146step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw23146step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23146 raw23146Labels = mixedMoment B node1486 node1486Labels := by
  calc
    mixedMoment B raw23146 raw23146Labels = mixedMoment B raw23146step0 raw23146step0Labels := by
      have hz : ∀ j, raw23146 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23146step0 = (fun i j => raw23146 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23146step0 raw23146; decide +kernel
      have hl : raw23146step0Labels = raw23146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23146 raw23146Labels permutation434 hz
    mixedMoment B raw23146step0 raw23146step0Labels = mixedMoment B raw23146step1 raw23146step1Labels := by
      have hz : ∀ j, raw23146step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23146step1 = (fun i j => raw23146step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23146step1 raw23146step0; decide +kernel
      have hl : raw23146step1Labels = raw23146step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23146step0 raw23146step0Labels permutation80 hz
    mixedMoment B raw23146step1 raw23146step1Labels = mixedMoment B raw23146step2 raw23146step2Labels := by
      have ha : raw23146step2 = (fun i j => raw23146step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23146step2 raw23146step1; decide +kernel
      have hl : raw23146step2Labels = raw23146step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23146step1 raw23146step1Labels permutation8 permutation7
    mixedMoment B raw23146step2 raw23146step2Labels = mixedMoment B raw23146step3 raw23146step3Labels := by
      have ha : raw23146step3 = raw23146step2 := by apply Matrix.ext; unfold raw23146step3 raw23146step2; decide +kernel
      have hl : raw23146step2Labels = labelEmbedding1 ∘ raw23146step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23146step2 raw23146step2Labels raw23146step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1486 node1486Labels := by rfl

def raw23147 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23147Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw23147step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23147step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw23147step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23147 raw23147Labels = mixedMoment B node1401 node1401Labels := by
  calc
    mixedMoment B raw23147 raw23147Labels = mixedMoment B raw23147step0 raw23147step0Labels := by
      have hz : ∀ j, raw23147 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23147step0 = (fun i j => raw23147 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23147step0 raw23147; decide +kernel
      have hl : raw23147step0Labels = raw23147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23147 raw23147Labels permutation434 hz
    mixedMoment B raw23147step0 raw23147step0Labels = mixedMoment B raw23147step1 raw23147step1Labels := by
      have ha : raw23147step1 = (fun i j => raw23147step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23147step1 raw23147step0; decide +kernel
      have hl : raw23147step1Labels = raw23147step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23147step0 raw23147step0Labels permutation32 permutation7
    mixedMoment B raw23147step1 raw23147step1Labels = mixedMoment B raw23147step2 raw23147step2Labels := by
      have ha : raw23147step2 = raw23147step1 := by apply Matrix.ext; unfold raw23147step2 raw23147step1; decide +kernel
      have hl : raw23147step1Labels = labelEmbedding1 ∘ raw23147step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23147step1 raw23147step1Labels raw23147step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1401 node1401Labels := by rfl

def raw23148 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23148Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23148step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23148step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw23148step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw23148step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23148step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw23148step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23148step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23148 raw23148Labels = mixedMoment B node1420 node1420Labels := by
  calc
    mixedMoment B raw23148 raw23148Labels = mixedMoment B raw23148step0 raw23148step0Labels := by
      have hz : ∀ j, raw23148 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23148step0 = (fun i j => raw23148 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23148step0 raw23148; decide +kernel
      have hl : raw23148step0Labels = raw23148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23148 raw23148Labels permutation434 hz
    mixedMoment B raw23148step0 raw23148step0Labels = mixedMoment B raw23148step1 raw23148step1Labels := by
      have hz : ∀ j, raw23148step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23148step1 = (fun i j => raw23148step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23148step1 raw23148step0; decide +kernel
      have hl : raw23148step1Labels = raw23148step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23148step0 raw23148step0Labels permutation80 hz
    mixedMoment B raw23148step1 raw23148step1Labels = mixedMoment B raw23148step2 raw23148step2Labels := by
      have ha : raw23148step2 = (fun i j => raw23148step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw23148step2 raw23148step1; decide +kernel
      have hl : raw23148step2Labels = raw23148step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23148step1 raw23148step1Labels permutation8 permutation7
    mixedMoment B raw23148step2 raw23148step2Labels = mixedMoment B raw23148step3 raw23148step3Labels := by
      have ha : raw23148step3 = raw23148step2 := by apply Matrix.ext; unfold raw23148step3 raw23148step2; decide +kernel
      have hl : raw23148step2Labels = labelEmbedding1 ∘ raw23148step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw23148step2 raw23148step2Labels raw23148step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1420 node1420Labels := by rfl

def raw23149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23149step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23149step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23149 raw23149Labels = mixedMoment B node4186 node4186Labels := by
  calc
    mixedMoment B raw23149 raw23149Labels = mixedMoment B raw23149step0 raw23149step0Labels := by
      have hz : ∀ j, raw23149 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23149step0 = (fun i j => raw23149 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23149step0 raw23149; decide +kernel
      have hl : raw23149step0Labels = raw23149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23149 raw23149Labels permutation434 hz
    mixedMoment B raw23149step0 raw23149step0Labels = mixedMoment B raw23149step1 raw23149step1Labels := by
      have hz : ∀ j, raw23149step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23149step1 = (fun i j => raw23149step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23149step1 raw23149step0; decide +kernel
      have hl : raw23149step1Labels = raw23149step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23149step0 raw23149step0Labels permutation80 hz
    _ = mixedMoment B node4186 node4186Labels := by rfl

def raw23150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23150step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23150 raw23150Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw23150 raw23150Labels = mixedMoment B raw23150step0 raw23150step0Labels := by
      have hz : ∀ j, raw23150 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23150step0 = (fun i j => raw23150 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23150step0 raw23150; decide +kernel
      have hl : raw23150step0Labels = raw23150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23150 raw23150Labels permutation434 hz
    mixedMoment B raw23150step0 raw23150step0Labels = mixedMoment B raw23150step1 raw23150step1Labels := by
      have ha : raw23150step1 = (fun i j => raw23150step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23150step1 raw23150step0; decide +kernel
      have hl : raw23150step1Labels = raw23150step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23150step0 raw23150step0Labels permutation38 permutation2
    _ = mixedMoment B node4355 node4355Labels := by rfl

def raw23151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23151step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23151step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23151 raw23151Labels = mixedMoment B node4355 node4355Labels := by
  calc
    mixedMoment B raw23151 raw23151Labels = mixedMoment B raw23151step0 raw23151step0Labels := by
      have hz : ∀ j, raw23151 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23151step0 = (fun i j => raw23151 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23151step0 raw23151; decide +kernel
      have hl : raw23151step0Labels = raw23151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23151 raw23151Labels permutation346 hz
    mixedMoment B raw23151step0 raw23151step0Labels = mixedMoment B raw23151step1 raw23151step1Labels := by
      have ha : raw23151step1 = (fun i j => raw23151step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23151step1 raw23151step0; decide +kernel
      have hl : raw23151step1Labels = raw23151step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23151step0 raw23151step0Labels permutation38 permutation2
    _ = mixedMoment B node4355 node4355Labels := by rfl

def raw23152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23152step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw23152step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23152step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw23152step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23152 raw23152Labels = mixedMoment B node4502 node4502Labels := by
  calc
    mixedMoment B raw23152 raw23152Labels = mixedMoment B raw23152step0 raw23152step0Labels := by
      have hz : ∀ j, raw23152 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23152step0 = (fun i j => raw23152 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23152step0 raw23152; decide +kernel
      have hl : raw23152step0Labels = raw23152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23152 raw23152Labels permutation434 hz
    mixedMoment B raw23152step0 raw23152step0Labels = mixedMoment B raw23152step1 raw23152step1Labels := by
      have hz : ∀ j, raw23152step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23152step1 = (fun i j => raw23152step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23152step1 raw23152step0; decide +kernel
      have hl : raw23152step1Labels = raw23152step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23152step0 raw23152step0Labels permutation80 hz
    mixedMoment B raw23152step1 raw23152step1Labels = mixedMoment B raw23152step2 raw23152step2Labels := by
      have ha : raw23152step2 = (fun i j => raw23152step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23152step2 raw23152step1; decide +kernel
      have hl : raw23152step2Labels = raw23152step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23152step1 raw23152step1Labels permutation9 permutation2
    _ = mixedMoment B node4502 node4502Labels := by rfl

def raw23153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23153step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23153 raw23153Labels = mixedMoment B node4155 node4155Labels := by
  calc
    mixedMoment B raw23153 raw23153Labels = mixedMoment B raw23153step0 raw23153step0Labels := by
      have hz : ∀ j, raw23153 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23153step0 = (fun i j => raw23153 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23153step0 raw23153; decide +kernel
      have hl : raw23153step0Labels = raw23153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23153 raw23153Labels permutation434 hz
    _ = mixedMoment B node4155 node4155Labels := by rfl

def raw23154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23154 raw23154Labels = mixedMoment B node4369 node4369Labels := by
  calc
    mixedMoment B raw23154 raw23154Labels = mixedMoment B raw23154step0 raw23154step0Labels := by
      have hz : ∀ j, raw23154 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23154step0 = (fun i j => raw23154 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23154step0 raw23154; decide +kernel
      have hl : raw23154step0Labels = raw23154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23154 raw23154Labels permutation434 hz
    _ = mixedMoment B node4369 node4369Labels := by rfl

def raw23155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23155 raw23155Labels = mixedMoment B node4329 node4329Labels := by
  calc
    mixedMoment B raw23155 raw23155Labels = mixedMoment B raw23155step0 raw23155step0Labels := by
      have ha : raw23155step0 = (fun i j => raw23155 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23155step0 raw23155; decide +kernel
      have hl : raw23155step0Labels = raw23155Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23155 raw23155Labels permutation200 permutation2
    _ = mixedMoment B node4329 node4329Labels := by rfl

def raw23156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23156step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23156 raw23156Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw23156 raw23156Labels = mixedMoment B raw23156step0 raw23156step0Labels := by
      have hz : ∀ j, raw23156 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23156step0 = (fun i j => raw23156 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23156step0 raw23156; decide +kernel
      have hl : raw23156step0Labels = raw23156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23156 raw23156Labels permutation434 hz
    mixedMoment B raw23156step0 raw23156step0Labels = mixedMoment B raw23156step1 raw23156step1Labels := by
      have ha : raw23156step1 = (fun i j => raw23156step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23156step1 raw23156step0; decide +kernel
      have hl : raw23156step1Labels = raw23156step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23156step0 raw23156step0Labels permutation33 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw23157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23157step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23157step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23157 raw23157Labels = mixedMoment B node4155 node4155Labels := by
  calc
    mixedMoment B raw23157 raw23157Labels = mixedMoment B raw23157step0 raw23157step0Labels := by
      have hz : ∀ j, raw23157 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23157step0 = (fun i j => raw23157 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23157step0 raw23157; decide +kernel
      have hl : raw23157step0Labels = raw23157Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23157 raw23157Labels permutation346 hz
    _ = mixedMoment B node4155 node4155Labels := by rfl

def raw23158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23158 raw23158Labels = mixedMoment B node4369 node4369Labels := by
  calc
    mixedMoment B raw23158 raw23158Labels = mixedMoment B raw23158step0 raw23158step0Labels := by
      have hz : ∀ j, raw23158 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23158step0 = (fun i j => raw23158 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23158step0 raw23158; decide +kernel
      have hl : raw23158step0Labels = raw23158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23158 raw23158Labels permutation346 hz
    _ = mixedMoment B node4369 node4369Labels := by rfl

def raw23159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23159 raw23159Labels = mixedMoment B node4329 node4329Labels := by
  calc
    mixedMoment B raw23159 raw23159Labels = mixedMoment B raw23159step0 raw23159step0Labels := by
      have ha : raw23159step0 = (fun i j => raw23159 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23159step0 raw23159; decide +kernel
      have hl : raw23159step0Labels = raw23159Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23159 raw23159Labels permutation176 permutation2
    _ = mixedMoment B node4329 node4329Labels := by rfl

def raw23160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw23160step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw23160step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23160 raw23160Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw23160 raw23160Labels = mixedMoment B raw23160step0 raw23160step0Labels := by
      have hz : ∀ j, raw23160 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23160step0 = (fun i j => raw23160 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23160step0 raw23160; decide +kernel
      have hl : raw23160step0Labels = raw23160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23160 raw23160Labels permutation346 hz
    mixedMoment B raw23160step0 raw23160step0Labels = mixedMoment B raw23160step1 raw23160step1Labels := by
      have ha : raw23160step1 = (fun i j => raw23160step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23160step1 raw23160step0; decide +kernel
      have hl : raw23160step1Labels = raw23160step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23160step0 raw23160step0Labels permutation33 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw23161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23161step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23161step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23161step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23161step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw23161step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23161 raw23161Labels = mixedMoment B node4161 node4161Labels := by
  calc
    mixedMoment B raw23161 raw23161Labels = mixedMoment B raw23161step0 raw23161step0Labels := by
      have hz : ∀ j, raw23161 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23161step0 = (fun i j => raw23161 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23161step0 raw23161; decide +kernel
      have hl : raw23161step0Labels = raw23161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23161 raw23161Labels permutation434 hz
    mixedMoment B raw23161step0 raw23161step0Labels = mixedMoment B raw23161step1 raw23161step1Labels := by
      have hz : ∀ j, raw23161step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23161step1 = (fun i j => raw23161step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23161step1 raw23161step0; decide +kernel
      have hl : raw23161step1Labels = raw23161step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23161step0 raw23161step0Labels permutation80 hz
    mixedMoment B raw23161step1 raw23161step1Labels = mixedMoment B raw23161step2 raw23161step2Labels := by
      have ha : raw23161step2 = (fun i j => raw23161step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23161step2 raw23161step1; decide +kernel
      have hl : raw23161step2Labels = raw23161step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23161step1 raw23161step1Labels permutation9 permutation2
    _ = mixedMoment B node4161 node4161Labels := by rfl

def raw23162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23162Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23162step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23162step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![3, -2, -1], ![2, -1, -1]]
def raw23162step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23162step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw23162step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23162 raw23162Labels = mixedMoment B node4374 node4374Labels := by
  calc
    mixedMoment B raw23162 raw23162Labels = mixedMoment B raw23162step0 raw23162step0Labels := by
      have hz : ∀ j, raw23162 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23162step0 = (fun i j => raw23162 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23162step0 raw23162; decide +kernel
      have hl : raw23162step0Labels = raw23162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23162 raw23162Labels permutation434 hz
    mixedMoment B raw23162step0 raw23162step0Labels = mixedMoment B raw23162step1 raw23162step1Labels := by
      have hz : ∀ j, raw23162step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23162step1 = (fun i j => raw23162step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23162step1 raw23162step0; decide +kernel
      have hl : raw23162step1Labels = raw23162step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23162step0 raw23162step0Labels permutation80 hz
    mixedMoment B raw23162step1 raw23162step1Labels = mixedMoment B raw23162step2 raw23162step2Labels := by
      have ha : raw23162step2 = (fun i j => raw23162step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23162step2 raw23162step1; decide +kernel
      have hl : raw23162step2Labels = raw23162step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23162step1 raw23162step1Labels permutation9 permutation2
    _ = mixedMoment B node4374 node4374Labels := by rfl

def raw23163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23163Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23163step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23163step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw23163step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23163 raw23163Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw23163 raw23163Labels = mixedMoment B raw23163step0 raw23163step0Labels := by
      have hz : ∀ j, raw23163 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23163step0 = (fun i j => raw23163 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23163step0 raw23163; decide +kernel
      have hl : raw23163step0Labels = raw23163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23163 raw23163Labels permutation434 hz
    mixedMoment B raw23163step0 raw23163step0Labels = mixedMoment B raw23163step1 raw23163step1Labels := by
      have ha : raw23163step1 = (fun i j => raw23163step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23163step1 raw23163step0; decide +kernel
      have hl : raw23163step1Labels = raw23163step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23163step0 raw23163step0Labels permutation39 permutation2
    _ = mixedMoment B node4335 node4335Labels := by rfl

def raw23164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23164Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw23164step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw23164step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23164 raw23164Labels = mixedMoment B node4335 node4335Labels := by
  calc
    mixedMoment B raw23164 raw23164Labels = mixedMoment B raw23164step0 raw23164step0Labels := by
      have hz : ∀ j, raw23164 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw23164step0 = (fun i j => raw23164 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw23164step0 raw23164; decide +kernel
      have hl : raw23164step0Labels = raw23164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23164 raw23164Labels permutation346 hz
    mixedMoment B raw23164step0 raw23164step0Labels = mixedMoment B raw23164step1 raw23164step1Labels := by
      have ha : raw23164step1 = (fun i j => raw23164step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23164step1 raw23164step0; decide +kernel
      have hl : raw23164step1Labels = raw23164step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23164step0 raw23164step0Labels permutation39 permutation2
    _ = mixedMoment B node4335 node4335Labels := by rfl

def raw23165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23165Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw23165step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23165step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![3, -2, -1], ![1, 0, -1]]
def raw23165step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw23165step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw23165step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical23165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23165 raw23165Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw23165 raw23165Labels = mixedMoment B raw23165step0 raw23165step0Labels := by
      have hz : ∀ j, raw23165 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23165step0 = (fun i j => raw23165 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23165step0 raw23165; decide +kernel
      have hl : raw23165step0Labels = raw23165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23165 raw23165Labels permutation434 hz
    mixedMoment B raw23165step0 raw23165step0Labels = mixedMoment B raw23165step1 raw23165step1Labels := by
      have hz : ∀ j, raw23165step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23165step1 = (fun i j => raw23165step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23165step1 raw23165step0; decide +kernel
      have hl : raw23165step1Labels = raw23165step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23165step0 raw23165step0Labels permutation80 hz
    mixedMoment B raw23165step1 raw23165step1Labels = mixedMoment B raw23165step2 raw23165step2Labels := by
      have ha : raw23165step2 = (fun i j => raw23165step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw23165step2 raw23165step1; decide +kernel
      have hl : raw23165step2Labels = raw23165step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23165step1 raw23165step1Labels permutation9 permutation2
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw23166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23166step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23166step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw23166step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23166step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw23166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23166 raw23166Labels = mixedMoment B node3188 node3188Labels := by
  calc
    mixedMoment B raw23166 raw23166Labels = mixedMoment B raw23166step0 raw23166step0Labels := by
      have hz : ∀ j, raw23166 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23166step0 = (fun i j => raw23166 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23166step0 raw23166; decide +kernel
      have hl : raw23166step0Labels = raw23166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23166 raw23166Labels permutation434 hz
    mixedMoment B raw23166step0 raw23166step0Labels = mixedMoment B raw23166step1 raw23166step1Labels := by
      have hz : ∀ j, raw23166step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw23166step1 = (fun i j => raw23166step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw23166step1 raw23166step0; decide +kernel
      have hl : raw23166step1Labels = raw23166step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23166step0 raw23166step0Labels permutation80 hz
    mixedMoment B raw23166step1 raw23166step1Labels = mixedMoment B raw23166step2 raw23166step2Labels := by
      have ha : raw23166step2 = (fun i j => raw23166step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23166step2 raw23166step1; decide +kernel
      have hl : raw23166step2Labels = raw23166step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23166step1 raw23166step1Labels permutation8 permutation3
    _ = mixedMoment B node3188 node3188Labels := by rfl

def raw23167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw23167step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw23167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw23167step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical23167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw23167 raw23167Labels = mixedMoment B node3207 node3207Labels := by
  calc
    mixedMoment B raw23167 raw23167Labels = mixedMoment B raw23167step0 raw23167step0Labels := by
      have hz : ∀ j, raw23167 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw23167step0 = (fun i j => raw23167 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw23167step0 raw23167; decide +kernel
      have hl : raw23167step0Labels = raw23167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw23167 raw23167Labels permutation434 hz
    mixedMoment B raw23167step0 raw23167step0Labels = mixedMoment B raw23167step1 raw23167step1Labels := by
      have ha : raw23167step1 = (fun i j => raw23167step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw23167step1 raw23167step0; decide +kernel
      have hl : raw23167step1Labels = raw23167step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw23167step0 raw23167step0Labels permutation38 permutation3
    _ = mixedMoment B node3207 node3207Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
