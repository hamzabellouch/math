import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17536Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17536step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17536step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17536step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17536 raw17536Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw17536 raw17536Labels = mixedMoment B raw17536step0 raw17536step0Labels := by
      have ha : raw17536step0 = (fun i j => raw17536 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17536step0 raw17536; decide +kernel
      have hl : raw17536step0Labels = raw17536Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17536 raw17536Labels permutation154 permutation3
    mixedMoment B raw17536step0 raw17536step0Labels = mixedMoment B raw17536step1 raw17536step1Labels := by
      have ha : raw17536step1 = raw17536step0 := by apply Matrix.ext; unfold raw17536step1 raw17536step0; decide +kernel
      have hl : raw17536step0Labels = labelEmbedding6 ∘ raw17536step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17536step0 raw17536step0Labels raw17536step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5138 node5138Labels := by rfl

def raw17537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17537Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17537step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17537step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17537step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17537 raw17537Labels = mixedMoment B node5419 node5419Labels := by
  calc
    mixedMoment B raw17537 raw17537Labels = mixedMoment B raw17537step0 raw17537step0Labels := by
      have ha : raw17537step0 = (fun i j => raw17537 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17537step0 raw17537; decide +kernel
      have hl : raw17537step0Labels = raw17537Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17537 raw17537Labels permutation687 permutation2
    mixedMoment B raw17537step0 raw17537step0Labels = mixedMoment B raw17537step1 raw17537step1Labels := by
      have ha : raw17537step1 = -raw17537step0 := by apply Matrix.ext; change ∀ i j, raw17537step1 i j = -(raw17537step0 i j); unfold raw17537step1 raw17537step0; decide +kernel
      have hl : raw17537step1Labels = raw17537step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5419 node5419Labels := by rfl

def raw17538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17538Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17538step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17538step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17538step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17538 raw17538Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw17538 raw17538Labels = mixedMoment B raw17538step0 raw17538step0Labels := by
      have ha : raw17538step0 = (fun i j => raw17538 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17538step0 raw17538; decide +kernel
      have hl : raw17538step0Labels = raw17538Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17538 raw17538Labels permutation688 permutation2
    mixedMoment B raw17538step0 raw17538step0Labels = mixedMoment B raw17538step1 raw17538step1Labels := by
      have ha : raw17538step1 = -raw17538step0 := by apply Matrix.ext; change ∀ i j, raw17538step1 i j = -(raw17538step0 i j); unfold raw17538step1 raw17538step0; decide +kernel
      have hl : raw17538step1Labels = raw17538step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5421 node5421Labels := by rfl

def raw17539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17539step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17539step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17539step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17539step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17539step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17539step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17539 raw17539Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw17539 raw17539Labels = mixedMoment B raw17539step0 raw17539step0Labels := by
      have hz : ∀ j, raw17539 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17539step0 = (fun i j => raw17539 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17539step0 raw17539; decide +kernel
      have hl : raw17539step0Labels = raw17539Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17539 raw17539Labels permutation520 hz
    mixedMoment B raw17539step0 raw17539step0Labels = mixedMoment B raw17539step1 raw17539step1Labels := by
      have ha : raw17539step1 = (fun i j => raw17539step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17539step1 raw17539step0; decide +kernel
      have hl : raw17539step1Labels = raw17539step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17539step0 raw17539step0Labels permutation145 permutation7
    mixedMoment B raw17539step1 raw17539step1Labels = mixedMoment B raw17539step2 raw17539step2Labels := by
      have ha : raw17539step2 = raw17539step1 := by apply Matrix.ext; unfold raw17539step2 raw17539step1; decide +kernel
      have hl : raw17539step1Labels = labelEmbedding10 ∘ raw17539step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17539step1 raw17539step1Labels raw17539step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw17540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17540Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17540 raw17540Labels = mixedMoment B node5480 node5480Labels := by
  calc
    _ = mixedMoment B node5480 node5480Labels := by rfl

def raw17541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17541step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17541step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17541step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17541 raw17541Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw17541 raw17541Labels = mixedMoment B raw17541step0 raw17541step0Labels := by
      have ha : raw17541step0 = (fun i j => raw17541 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17541step0 raw17541; decide +kernel
      have hl : raw17541step0Labels = raw17541Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17541 raw17541Labels permutation153 permutation3
    mixedMoment B raw17541step0 raw17541step0Labels = mixedMoment B raw17541step1 raw17541step1Labels := by
      have ha : raw17541step1 = raw17541step0 := by apply Matrix.ext; unfold raw17541step1 raw17541step0; decide +kernel
      have hl : raw17541step0Labels = labelEmbedding6 ∘ raw17541step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17541step0 raw17541step0Labels raw17541step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5129 node5129Labels := by rfl

def raw17542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17542step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17542step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17542step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17542 raw17542Labels = mixedMoment B node5377 node5377Labels := by
  calc
    mixedMoment B raw17542 raw17542Labels = mixedMoment B raw17542step0 raw17542step0Labels := by
      have ha : raw17542step0 = (fun i j => raw17542 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17542step0 raw17542; decide +kernel
      have hl : raw17542step0Labels = raw17542Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17542 raw17542Labels permutation681 permutation2
    mixedMoment B raw17542step0 raw17542step0Labels = mixedMoment B raw17542step1 raw17542step1Labels := by
      have ha : raw17542step1 = -raw17542step0 := by apply Matrix.ext; change ∀ i j, raw17542step1 i j = -(raw17542step0 i j); unfold raw17542step1 raw17542step0; decide +kernel
      have hl : raw17542step1Labels = raw17542step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5377 node5377Labels := by rfl

def raw17543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17543step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17543step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17543step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17543step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17543step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17543 raw17543Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw17543 raw17543Labels = mixedMoment B raw17543step0 raw17543step0Labels := by
      have ha : raw17543step0 = (fun i j => raw17543 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17543step0 raw17543; decide +kernel
      have hl : raw17543step0Labels = raw17543Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17543 raw17543Labels permutation587 permutation3
    mixedMoment B raw17543step0 raw17543step0Labels = mixedMoment B raw17543step1 raw17543step1Labels := by
      have ha : raw17543step1 = -raw17543step0 := by apply Matrix.ext; change ∀ i j, raw17543step1 i j = -(raw17543step0 i j); unfold raw17543step1 raw17543step0; decide +kernel
      have hl : raw17543step1Labels = raw17543step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17543step1 raw17543step1Labels = mixedMoment B raw17543step2 raw17543step2Labels := by
      have ha : raw17543step2 = raw17543step1 := by apply Matrix.ext; unfold raw17543step2 raw17543step1; decide +kernel
      have hl : raw17543step1Labels = labelEmbedding6 ∘ raw17543step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17543step1 raw17543step1Labels raw17543step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw17544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17544step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17544 raw17544Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw17544 raw17544Labels = mixedMoment B raw17544step0 raw17544step0Labels := by
      have ha : raw17544step0 = (fun i j => raw17544 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17544step0 raw17544; decide +kernel
      have hl : raw17544step0Labels = raw17544Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17544 raw17544Labels permutation680 permutation2
    mixedMoment B raw17544step0 raw17544step0Labels = mixedMoment B raw17544step1 raw17544step1Labels := by
      have ha : raw17544step1 = -raw17544step0 := by apply Matrix.ext; change ∀ i j, raw17544step1 i j = -(raw17544step0 i j); unfold raw17544step1 raw17544step0; decide +kernel
      have hl : raw17544step1Labels = raw17544step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw17545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw17545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17545step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17545step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17545 raw17545Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw17545 raw17545Labels = mixedMoment B raw17545step0 raw17545step0Labels := by
      have ha : raw17545step0 = (fun i j => raw17545 (permutation559 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17545step0 raw17545; decide +kernel
      have hl : raw17545step0Labels = raw17545Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17545 raw17545Labels permutation559 permutation5
    mixedMoment B raw17545step0 raw17545step0Labels = mixedMoment B raw17545step1 raw17545step1Labels := by
      have ha : raw17545step1 = raw17545step0 := by apply Matrix.ext; unfold raw17545step1 raw17545step0; decide +kernel
      have hl : raw17545step0Labels = labelEmbedding8 ∘ raw17545step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17545step0 raw17545step0Labels raw17545step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw17546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw17546step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17546step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw17546step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17546 raw17546Labels = mixedMoment B node5128 node5128Labels := by
  calc
    mixedMoment B raw17546 raw17546Labels = mixedMoment B raw17546step0 raw17546step0Labels := by
      have ha : raw17546step0 = (fun i j => raw17546 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17546step0 raw17546; decide +kernel
      have hl : raw17546step0Labels = raw17546Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17546 raw17546Labels permutation682 permutation2
    mixedMoment B raw17546step0 raw17546step0Labels = mixedMoment B raw17546step1 raw17546step1Labels := by
      have ha : raw17546step1 = -raw17546step0 := by apply Matrix.ext; change ∀ i j, raw17546step1 i j = -(raw17546step0 i j); unfold raw17546step1 raw17546step0; decide +kernel
      have hl : raw17546step1Labels = raw17546step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5128 node5128Labels := by rfl

def raw17547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17547step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17547step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17547 raw17547Labels = mixedMoment B node5130 node5130Labels := by
  calc
    mixedMoment B raw17547 raw17547Labels = mixedMoment B raw17547step0 raw17547step0Labels := by
      have ha : raw17547step0 = (fun i j => raw17547 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17547step0 raw17547; decide +kernel
      have hl : raw17547step0Labels = raw17547Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17547 raw17547Labels permutation681 permutation2
    mixedMoment B raw17547step0 raw17547step0Labels = mixedMoment B raw17547step1 raw17547step1Labels := by
      have ha : raw17547step1 = -raw17547step0 := by apply Matrix.ext; change ∀ i j, raw17547step1 i j = -(raw17547step0 i j); unfold raw17547step1 raw17547step0; decide +kernel
      have hl : raw17547step1Labels = raw17547step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5130 node5130Labels := by rfl

def raw17548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17548step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17548step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17548 raw17548Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw17548 raw17548Labels = mixedMoment B raw17548step0 raw17548step0Labels := by
      have ha : raw17548step0 = (fun i j => raw17548 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17548step0 raw17548; decide +kernel
      have hl : raw17548step0Labels = raw17548Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17548 raw17548Labels permutation688 permutation2
    mixedMoment B raw17548step0 raw17548step0Labels = mixedMoment B raw17548step1 raw17548step1Labels := by
      have ha : raw17548step1 = -raw17548step0 := by apply Matrix.ext; change ∀ i j, raw17548step1 i j = -(raw17548step0 i j); unfold raw17548step1 raw17548step0; decide +kernel
      have hl : raw17548step1Labels = raw17548step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw17549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17549step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17549step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17549 raw17549Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw17549 raw17549Labels = mixedMoment B raw17549step0 raw17549step0Labels := by
      have ha : raw17549step0 = (fun i j => raw17549 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17549step0 raw17549; decide +kernel
      have hl : raw17549step0Labels = raw17549Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17549 raw17549Labels permutation680 permutation2
    mixedMoment B raw17549step0 raw17549step0Labels = mixedMoment B raw17549step1 raw17549step1Labels := by
      have ha : raw17549step1 = -raw17549step0 := by apply Matrix.ext; change ∀ i j, raw17549step1 i j = -(raw17549step0 i j); unfold raw17549step1 raw17549step0; decide +kernel
      have hl : raw17549step1Labels = raw17549step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5137 node5137Labels := by rfl

def raw17550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw17550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw17550step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17550step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17550step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17550 raw17550Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw17550 raw17550Labels = mixedMoment B raw17550step0 raw17550step0Labels := by
      have hz : ∀ j, raw17550 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17550step0 = (fun i j => raw17550 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17550step0 raw17550; decide +kernel
      have hl : raw17550step0Labels = raw17550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17550 raw17550Labels permutation520 hz
    mixedMoment B raw17550step0 raw17550step0Labels = mixedMoment B raw17550step1 raw17550step1Labels := by
      have ha : raw17550step1 = (fun i j => raw17550step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17550step1 raw17550step0; decide +kernel
      have hl : raw17550step1Labels = raw17550step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17550step0 raw17550step0Labels permutation145 permutation2
    mixedMoment B raw17550step1 raw17550step1Labels = mixedMoment B raw17550step2 raw17550step2Labels := by
      have ha : raw17550step2 = -raw17550step1 := by apply Matrix.ext; change ∀ i j, raw17550step2 i j = -(raw17550step1 i j); unfold raw17550step2 raw17550step1; decide +kernel
      have hl : raw17550step2Labels = raw17550step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw17551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17551Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17551step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17551step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17551step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17551 raw17551Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw17551 raw17551Labels = mixedMoment B raw17551step0 raw17551step0Labels := by
      have ha : raw17551step0 = (fun i j => raw17551 (permutation645 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17551step0 raw17551; decide +kernel
      have hl : raw17551step0Labels = raw17551Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17551 raw17551Labels permutation645 permutation7
    mixedMoment B raw17551step0 raw17551step0Labels = mixedMoment B raw17551step1 raw17551step1Labels := by
      have ha : raw17551step1 = raw17551step0 := by apply Matrix.ext; unfold raw17551step1 raw17551step0; decide +kernel
      have hl : raw17551step0Labels = labelEmbedding1 ∘ raw17551step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17551step0 raw17551step0Labels raw17551step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw17552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17552Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17552step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17552step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17552 raw17552Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw17552 raw17552Labels = mixedMoment B raw17552step0 raw17552step0Labels := by
      have ha : raw17552step0 = (fun i j => raw17552 (permutation645 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17552step0 raw17552; decide +kernel
      have hl : raw17552step0Labels = raw17552Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17552 raw17552Labels permutation645 permutation7
    mixedMoment B raw17552step0 raw17552step0Labels = mixedMoment B raw17552step1 raw17552step1Labels := by
      have ha : raw17552step1 = raw17552step0 := by apply Matrix.ext; unfold raw17552step1 raw17552step0; decide +kernel
      have hl : raw17552step0Labels = labelEmbedding1 ∘ raw17552step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17552step0 raw17552step0Labels raw17552step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw17553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17553Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17553step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw17553step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17553step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw17553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17553 raw17553Labels = mixedMoment B node3844 node3844Labels := by
  calc
    mixedMoment B raw17553 raw17553Labels = mixedMoment B raw17553step0 raw17553step0Labels := by
      have ha : raw17553step0 = (fun i j => raw17553 (permutation641 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17553step0 raw17553; decide +kernel
      have hl : raw17553step0Labels = raw17553Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17553 raw17553Labels permutation641 permutation7
    mixedMoment B raw17553step0 raw17553step0Labels = mixedMoment B raw17553step1 raw17553step1Labels := by
      have ha : raw17553step1 = raw17553step0 := by apply Matrix.ext; unfold raw17553step1 raw17553step0; decide +kernel
      have hl : raw17553step0Labels = labelEmbedding1 ∘ raw17553step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17553step0 raw17553step0Labels raw17553step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3844 node3844Labels := by rfl

def raw17554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17554Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17554step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17554step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17554step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17554 raw17554Labels = mixedMoment B node3859 node3859Labels := by
  calc
    mixedMoment B raw17554 raw17554Labels = mixedMoment B raw17554step0 raw17554step0Labels := by
      have hz : ∀ j, raw17554 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17554step0 = (fun i j => raw17554 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17554step0 raw17554; decide +kernel
      have hl : raw17554step0Labels = raw17554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17554 raw17554Labels permutation520 hz
    mixedMoment B raw17554step0 raw17554step0Labels = mixedMoment B raw17554step1 raw17554step1Labels := by
      have ha : raw17554step1 = (fun i j => raw17554step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17554step1 raw17554step0; decide +kernel
      have hl : raw17554step1Labels = raw17554step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17554step0 raw17554step0Labels permutation144 permutation7
    mixedMoment B raw17554step1 raw17554step1Labels = mixedMoment B raw17554step2 raw17554step2Labels := by
      have ha : raw17554step2 = raw17554step1 := by apply Matrix.ext; unfold raw17554step2 raw17554step1; decide +kernel
      have hl : raw17554step1Labels = labelEmbedding1 ∘ raw17554step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17554step1 raw17554step1Labels raw17554step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3859 node3859Labels := by rfl

def raw17555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17555Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17555step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17555step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17555 raw17555Labels = mixedMoment B node3992 node3992Labels := by
  calc
    mixedMoment B raw17555 raw17555Labels = mixedMoment B raw17555step0 raw17555step0Labels := by
      have ha : raw17555step0 = (fun i j => raw17555 (permutation645 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17555step0 raw17555; decide +kernel
      have hl : raw17555step0Labels = raw17555Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17555 raw17555Labels permutation645 permutation7
    mixedMoment B raw17555step0 raw17555step0Labels = mixedMoment B raw17555step1 raw17555step1Labels := by
      have ha : raw17555step1 = raw17555step0 := by apply Matrix.ext; unfold raw17555step1 raw17555step0; decide +kernel
      have hl : raw17555step0Labels = labelEmbedding1 ∘ raw17555step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17555step0 raw17555step0Labels raw17555step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3992 node3992Labels := by rfl

def raw17556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17556Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17556step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17556step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17556step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17556step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17556 raw17556Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw17556 raw17556Labels = mixedMoment B raw17556step0 raw17556step0Labels := by
      have ha : raw17556step0 = (fun i j => raw17556 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17556step0 raw17556; decide +kernel
      have hl : raw17556step0Labels = raw17556Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17556 raw17556Labels permutation194 permutation5
    mixedMoment B raw17556step0 raw17556step0Labels = mixedMoment B raw17556step1 raw17556step1Labels := by
      have ha : raw17556step1 = -raw17556step0 := by apply Matrix.ext; change ∀ i j, raw17556step1 i j = -(raw17556step0 i j); unfold raw17556step1 raw17556step0; decide +kernel
      have hl : raw17556step1Labels = raw17556step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17556step1 raw17556step1Labels = mixedMoment B raw17556step2 raw17556step2Labels := by
      have ha : raw17556step2 = raw17556step1 := by apply Matrix.ext; unfold raw17556step2 raw17556step1; decide +kernel
      have hl : raw17556step1Labels = labelEmbedding1 ∘ raw17556step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17556step1 raw17556step1Labels raw17556step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

def raw17557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17557Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17557step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17557step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17557step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17557 raw17557Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw17557 raw17557Labels = mixedMoment B raw17557step0 raw17557step0Labels := by
      have ha : raw17557step0 = (fun i j => raw17557 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17557step0 raw17557; decide +kernel
      have hl : raw17557step0Labels = raw17557Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17557 raw17557Labels permutation644 permutation7
    mixedMoment B raw17557step0 raw17557step0Labels = mixedMoment B raw17557step1 raw17557step1Labels := by
      have ha : raw17557step1 = raw17557step0 := by apply Matrix.ext; unfold raw17557step1 raw17557step0; decide +kernel
      have hl : raw17557step0Labels = labelEmbedding1 ∘ raw17557step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17557step0 raw17557step0Labels raw17557step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3874 node3874Labels := by rfl

def raw17558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17558Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17558step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17558step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17558 raw17558Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw17558 raw17558Labels = mixedMoment B raw17558step0 raw17558step0Labels := by
      have ha : raw17558step0 = (fun i j => raw17558 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17558step0 raw17558; decide +kernel
      have hl : raw17558step0Labels = raw17558Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17558 raw17558Labels permutation644 permutation7
    mixedMoment B raw17558step0 raw17558step0Labels = mixedMoment B raw17558step1 raw17558step1Labels := by
      have ha : raw17558step1 = raw17558step0 := by apply Matrix.ext; unfold raw17558step1 raw17558step0; decide +kernel
      have hl : raw17558step0Labels = labelEmbedding1 ∘ raw17558step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17558step0 raw17558step0Labels raw17558step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw17559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17559Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17559step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17559step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17559step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17559step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17559 raw17559Labels = mixedMoment B node3858 node3858Labels := by
  calc
    mixedMoment B raw17559 raw17559Labels = mixedMoment B raw17559step0 raw17559step0Labels := by
      have hz : ∀ j, raw17559 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17559step0 = (fun i j => raw17559 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17559step0 raw17559; decide +kernel
      have hl : raw17559step0Labels = raw17559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17559 raw17559Labels permutation520 hz
    mixedMoment B raw17559step0 raw17559step0Labels = mixedMoment B raw17559step1 raw17559step1Labels := by
      have ha : raw17559step1 = (fun i j => raw17559step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17559step1 raw17559step0; decide +kernel
      have hl : raw17559step1Labels = raw17559step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17559step0 raw17559step0Labels permutation143 permutation7
    mixedMoment B raw17559step1 raw17559step1Labels = mixedMoment B raw17559step2 raw17559step2Labels := by
      have ha : raw17559step2 = raw17559step1 := by apply Matrix.ext; unfold raw17559step2 raw17559step1; decide +kernel
      have hl : raw17559step1Labels = labelEmbedding1 ∘ raw17559step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17559step1 raw17559step1Labels raw17559step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3858 node3858Labels := by rfl

def raw17560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17560Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17560step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17560step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17560 raw17560Labels = mixedMoment B node3991 node3991Labels := by
  calc
    mixedMoment B raw17560 raw17560Labels = mixedMoment B raw17560step0 raw17560step0Labels := by
      have ha : raw17560step0 = (fun i j => raw17560 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17560step0 raw17560; decide +kernel
      have hl : raw17560step0Labels = raw17560Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17560 raw17560Labels permutation644 permutation7
    mixedMoment B raw17560step0 raw17560step0Labels = mixedMoment B raw17560step1 raw17560step1Labels := by
      have ha : raw17560step1 = raw17560step0 := by apply Matrix.ext; unfold raw17560step1 raw17560step0; decide +kernel
      have hl : raw17560step0Labels = labelEmbedding1 ∘ raw17560step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17560step0 raw17560step0Labels raw17560step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3991 node3991Labels := by rfl

def raw17561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17561Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw17561step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17561step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw17561step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17561step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw17561step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17561 raw17561Labels = mixedMoment B node3605 node3605Labels := by
  calc
    mixedMoment B raw17561 raw17561Labels = mixedMoment B raw17561step0 raw17561step0Labels := by
      have ha : raw17561step0 = (fun i j => raw17561 (permutation156 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17561step0 raw17561; decide +kernel
      have hl : raw17561step0Labels = raw17561Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17561 raw17561Labels permutation156 permutation5
    mixedMoment B raw17561step0 raw17561step0Labels = mixedMoment B raw17561step1 raw17561step1Labels := by
      have ha : raw17561step1 = -raw17561step0 := by apply Matrix.ext; change ∀ i j, raw17561step1 i j = -(raw17561step0 i j); unfold raw17561step1 raw17561step0; decide +kernel
      have hl : raw17561step1Labels = raw17561step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17561step1 raw17561step1Labels = mixedMoment B raw17561step2 raw17561step2Labels := by
      have ha : raw17561step2 = raw17561step1 := by apply Matrix.ext; unfold raw17561step2 raw17561step1; decide +kernel
      have hl : raw17561step1Labels = labelEmbedding1 ∘ raw17561step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17561step1 raw17561step1Labels raw17561step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3605 node3605Labels := by rfl

def raw17562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17562Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17562step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17562step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17562step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17562 raw17562Labels = mixedMoment B node3797 node3797Labels := by
  calc
    mixedMoment B raw17562 raw17562Labels = mixedMoment B raw17562step0 raw17562step0Labels := by
      have ha : raw17562step0 = (fun i j => raw17562 (permutation645 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17562step0 raw17562; decide +kernel
      have hl : raw17562step0Labels = raw17562Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17562 raw17562Labels permutation645 permutation7
    mixedMoment B raw17562step0 raw17562step0Labels = mixedMoment B raw17562step1 raw17562step1Labels := by
      have ha : raw17562step1 = raw17562step0 := by apply Matrix.ext; unfold raw17562step1 raw17562step0; decide +kernel
      have hl : raw17562step0Labels = labelEmbedding1 ∘ raw17562step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17562step0 raw17562step0Labels raw17562step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3797 node3797Labels := by rfl

def raw17563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17563Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17563step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17563step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17563step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17563 raw17563Labels = mixedMoment B node3798 node3798Labels := by
  calc
    mixedMoment B raw17563 raw17563Labels = mixedMoment B raw17563step0 raw17563step0Labels := by
      have ha : raw17563step0 = (fun i j => raw17563 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17563step0 raw17563; decide +kernel
      have hl : raw17563step0Labels = raw17563Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17563 raw17563Labels permutation644 permutation7
    mixedMoment B raw17563step0 raw17563step0Labels = mixedMoment B raw17563step1 raw17563step1Labels := by
      have ha : raw17563step1 = raw17563step0 := by apply Matrix.ext; unfold raw17563step1 raw17563step0; decide +kernel
      have hl : raw17563step0Labels = labelEmbedding1 ∘ raw17563step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17563step0 raw17563step0Labels raw17563step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3798 node3798Labels := by rfl

def raw17564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17564Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17564step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17564step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17564step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17564step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17564 raw17564Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw17564 raw17564Labels = mixedMoment B raw17564step0 raw17564step0Labels := by
      have hz : ∀ j, raw17564 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17564step0 = (fun i j => raw17564 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17564step0 raw17564; decide +kernel
      have hl : raw17564step0Labels = raw17564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17564 raw17564Labels permutation520 hz
    mixedMoment B raw17564step0 raw17564step0Labels = mixedMoment B raw17564step1 raw17564step1Labels := by
      have ha : raw17564step1 = (fun i j => raw17564step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17564step1 raw17564step0; decide +kernel
      have hl : raw17564step1Labels = raw17564step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17564step0 raw17564step0Labels permutation145 permutation7
    mixedMoment B raw17564step1 raw17564step1Labels = mixedMoment B raw17564step2 raw17564step2Labels := by
      have ha : raw17564step2 = raw17564step1 := by apply Matrix.ext; unfold raw17564step2 raw17564step1; decide +kernel
      have hl : raw17564step1Labels = labelEmbedding1 ∘ raw17564step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17564step1 raw17564step1Labels raw17564step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

def raw17565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17565Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17565step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17565step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17565step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17565 raw17565Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw17565 raw17565Labels = mixedMoment B raw17565step0 raw17565step0Labels := by
      have ha : raw17565step0 = (fun i j => raw17565 (permutation646 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17565step0 raw17565; decide +kernel
      have hl : raw17565step0Labels = raw17565Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17565 raw17565Labels permutation646 permutation7
    mixedMoment B raw17565step0 raw17565step0Labels = mixedMoment B raw17565step1 raw17565step1Labels := by
      have ha : raw17565step1 = raw17565step0 := by apply Matrix.ext; unfold raw17565step1 raw17565step0; decide +kernel
      have hl : raw17565step0Labels = labelEmbedding1 ∘ raw17565step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17565step0 raw17565step0Labels raw17565step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw17566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17566Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17566step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17566step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17566step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17566step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17566 raw17566Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw17566 raw17566Labels = mixedMoment B raw17566step0 raw17566step0Labels := by
      have ha : raw17566step0 = (fun i j => raw17566 (permutation181 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17566step0 raw17566; decide +kernel
      have hl : raw17566step0Labels = raw17566Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17566 raw17566Labels permutation181 permutation5
    mixedMoment B raw17566step0 raw17566step0Labels = mixedMoment B raw17566step1 raw17566step1Labels := by
      have ha : raw17566step1 = -raw17566step0 := by apply Matrix.ext; change ∀ i j, raw17566step1 i j = -(raw17566step0 i j); unfold raw17566step1 raw17566step0; decide +kernel
      have hl : raw17566step1Labels = raw17566step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17566step1 raw17566step1Labels = mixedMoment B raw17566step2 raw17566step2Labels := by
      have ha : raw17566step2 = raw17566step1 := by apply Matrix.ext; unfold raw17566step2 raw17566step1; decide +kernel
      have hl : raw17566step1Labels = labelEmbedding1 ∘ raw17566step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17566step1 raw17566step1Labels raw17566step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

def raw17567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17567Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17567step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17567step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17567step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17567 raw17567Labels = mixedMoment B node3842 node3842Labels := by
  calc
    mixedMoment B raw17567 raw17567Labels = mixedMoment B raw17567step0 raw17567step0Labels := by
      have ha : raw17567step0 = (fun i j => raw17567 (permutation645 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17567step0 raw17567; decide +kernel
      have hl : raw17567step0Labels = raw17567Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17567 raw17567Labels permutation645 permutation7
    mixedMoment B raw17567step0 raw17567step0Labels = mixedMoment B raw17567step1 raw17567step1Labels := by
      have ha : raw17567step1 = raw17567step0 := by apply Matrix.ext; unfold raw17567step1 raw17567step0; decide +kernel
      have hl : raw17567step0Labels = labelEmbedding1 ∘ raw17567step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17567step0 raw17567step0Labels raw17567step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3842 node3842Labels := by rfl

def raw17568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17568Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17568step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17568step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17568step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17568 raw17568Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw17568 raw17568Labels = mixedMoment B raw17568step0 raw17568step0Labels := by
      have ha : raw17568step0 = (fun i j => raw17568 (permutation646 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17568step0 raw17568; decide +kernel
      have hl : raw17568step0Labels = raw17568Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17568 raw17568Labels permutation646 permutation7
    mixedMoment B raw17568step0 raw17568step0Labels = mixedMoment B raw17568step1 raw17568step1Labels := by
      have ha : raw17568step1 = raw17568step0 := by apply Matrix.ext; unfold raw17568step1 raw17568step0; decide +kernel
      have hl : raw17568step0Labels = labelEmbedding1 ∘ raw17568step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17568step0 raw17568step0Labels raw17568step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3873 node3873Labels := by rfl

def raw17569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17569Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17569step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17569step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17569step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17569step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17569step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17569step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17569 raw17569Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw17569 raw17569Labels = mixedMoment B raw17569step0 raw17569step0Labels := by
      have hz : ∀ j, raw17569 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17569step0 = (fun i j => raw17569 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17569step0 raw17569; decide +kernel
      have hl : raw17569step0Labels = raw17569Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17569 raw17569Labels permutation520 hz
    mixedMoment B raw17569step0 raw17569step0Labels = mixedMoment B raw17569step1 raw17569step1Labels := by
      have ha : raw17569step1 = (fun i j => raw17569step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17569step1 raw17569step0; decide +kernel
      have hl : raw17569step1Labels = raw17569step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17569step0 raw17569step0Labels permutation145 permutation7
    mixedMoment B raw17569step1 raw17569step1Labels = mixedMoment B raw17569step2 raw17569step2Labels := by
      have ha : raw17569step2 = raw17569step1 := by apply Matrix.ext; unfold raw17569step2 raw17569step1; decide +kernel
      have hl : raw17569step1Labels = labelEmbedding1 ∘ raw17569step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17569step1 raw17569step1Labels raw17569step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw17570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17570Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17570step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17570step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17570step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17570 raw17570Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw17570 raw17570Labels = mixedMoment B raw17570step0 raw17570step0Labels := by
      have ha : raw17570step0 = (fun i j => raw17570 (permutation494 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17570step0 raw17570; decide +kernel
      have hl : raw17570step0Labels = raw17570Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17570 raw17570Labels permutation494 permutation5
    mixedMoment B raw17570step0 raw17570step0Labels = mixedMoment B raw17570step1 raw17570step1Labels := by
      have ha : raw17570step1 = raw17570step0 := by apply Matrix.ext; unfold raw17570step1 raw17570step0; decide +kernel
      have hl : raw17570step0Labels = labelEmbedding1 ∘ raw17570step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17570step0 raw17570step0Labels raw17570step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw17571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17571Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw17571step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17571step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw17571step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17571step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw17571step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17571 raw17571Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw17571 raw17571Labels = mixedMoment B raw17571step0 raw17571step0Labels := by
      have ha : raw17571step0 = (fun i j => raw17571 (permutation180 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17571step0 raw17571; decide +kernel
      have hl : raw17571step0Labels = raw17571Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17571 raw17571Labels permutation180 permutation5
    mixedMoment B raw17571step0 raw17571step0Labels = mixedMoment B raw17571step1 raw17571step1Labels := by
      have ha : raw17571step1 = -raw17571step0 := by apply Matrix.ext; change ∀ i j, raw17571step1 i j = -(raw17571step0 i j); unfold raw17571step1 raw17571step0; decide +kernel
      have hl : raw17571step1Labels = raw17571step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17571step1 raw17571step1Labels = mixedMoment B raw17571step2 raw17571step2Labels := by
      have ha : raw17571step2 = raw17571step1 := by apply Matrix.ext; unfold raw17571step2 raw17571step1; decide +kernel
      have hl : raw17571step1Labels = labelEmbedding1 ∘ raw17571step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17571step1 raw17571step1Labels raw17571step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

def raw17572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17572Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17572step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17572step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17572step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17572 raw17572Labels = mixedMoment B node3835 node3835Labels := by
  calc
    mixedMoment B raw17572 raw17572Labels = mixedMoment B raw17572step0 raw17572step0Labels := by
      have ha : raw17572step0 = (fun i j => raw17572 (permutation567 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17572step0 raw17572; decide +kernel
      have hl : raw17572step0Labels = raw17572Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17572 raw17572Labels permutation567 permutation5
    mixedMoment B raw17572step0 raw17572step0Labels = mixedMoment B raw17572step1 raw17572step1Labels := by
      have ha : raw17572step1 = raw17572step0 := by apply Matrix.ext; unfold raw17572step1 raw17572step0; decide +kernel
      have hl : raw17572step0Labels = labelEmbedding1 ∘ raw17572step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17572step0 raw17572step0Labels raw17572step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3835 node3835Labels := by rfl

def raw17573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17573Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17573step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17573step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17573step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17573 raw17573Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw17573 raw17573Labels = mixedMoment B raw17573step0 raw17573step0Labels := by
      have ha : raw17573step0 = (fun i j => raw17573 (permutation565 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17573step0 raw17573; decide +kernel
      have hl : raw17573step0Labels = raw17573Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17573 raw17573Labels permutation565 permutation5
    mixedMoment B raw17573step0 raw17573step0Labels = mixedMoment B raw17573step1 raw17573step1Labels := by
      have ha : raw17573step1 = raw17573step0 := by apply Matrix.ext; unfold raw17573step1 raw17573step0; decide +kernel
      have hl : raw17573step0Labels = labelEmbedding1 ∘ raw17573step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17573step0 raw17573step0Labels raw17573step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw17574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw17574Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17574step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17574step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17574 raw17574Labels = mixedMoment B node3836 node3836Labels := by
  calc
    mixedMoment B raw17574 raw17574Labels = mixedMoment B raw17574step0 raw17574step0Labels := by
      have ha : raw17574step0 = (fun i j => raw17574 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17574step0 raw17574; decide +kernel
      have hl : raw17574step0Labels = raw17574Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17574 raw17574Labels permutation644 permutation7
    mixedMoment B raw17574step0 raw17574step0Labels = mixedMoment B raw17574step1 raw17574step1Labels := by
      have ha : raw17574step1 = raw17574step0 := by apply Matrix.ext; unfold raw17574step1 raw17574step0; decide +kernel
      have hl : raw17574step0Labels = labelEmbedding1 ∘ raw17574step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17574step0 raw17574step0Labels raw17574step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3836 node3836Labels := by rfl

def raw17575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw17575Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17575step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17575step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17575 raw17575Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw17575 raw17575Labels = mixedMoment B raw17575step0 raw17575step0Labels := by
      have ha : raw17575step0 = (fun i j => raw17575 (permutation559 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17575step0 raw17575; decide +kernel
      have hl : raw17575step0Labels = raw17575Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17575 raw17575Labels permutation559 permutation5
    mixedMoment B raw17575step0 raw17575step0Labels = mixedMoment B raw17575step1 raw17575step1Labels := by
      have ha : raw17575step1 = raw17575step0 := by apply Matrix.ext; unfold raw17575step1 raw17575step0; decide +kernel
      have hl : raw17575step0Labels = labelEmbedding1 ∘ raw17575step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17575step0 raw17575step0Labels raw17575step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw17576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17576Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw17576step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17576step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw17576step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17576step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw17576step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17576 raw17576Labels = mixedMoment B node3519 node3519Labels := by
  calc
    mixedMoment B raw17576 raw17576Labels = mixedMoment B raw17576step0 raw17576step0Labels := by
      have ha : raw17576step0 = (fun i j => raw17576 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17576step0 raw17576; decide +kernel
      have hl : raw17576step0Labels = raw17576Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17576 raw17576Labels permutation176 permutation5
    mixedMoment B raw17576step0 raw17576step0Labels = mixedMoment B raw17576step1 raw17576step1Labels := by
      have ha : raw17576step1 = -raw17576step0 := by apply Matrix.ext; change ∀ i j, raw17576step1 i j = -(raw17576step0 i j); unfold raw17576step1 raw17576step0; decide +kernel
      have hl : raw17576step1Labels = raw17576step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17576step1 raw17576step1Labels = mixedMoment B raw17576step2 raw17576step2Labels := by
      have ha : raw17576step2 = raw17576step1 := by apply Matrix.ext; unfold raw17576step2 raw17576step1; decide +kernel
      have hl : raw17576step1Labels = labelEmbedding1 ∘ raw17576step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17576step1 raw17576step1Labels raw17576step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3519 node3519Labels := by rfl

def raw17577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17577Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17577step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17577step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17577 raw17577Labels = mixedMoment B node3520 node3520Labels := by
  calc
    mixedMoment B raw17577 raw17577Labels = mixedMoment B raw17577step0 raw17577step0Labels := by
      have ha : raw17577step0 = (fun i j => raw17577 (permutation645 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17577step0 raw17577; decide +kernel
      have hl : raw17577step0Labels = raw17577Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17577 raw17577Labels permutation645 permutation7
    mixedMoment B raw17577step0 raw17577step0Labels = mixedMoment B raw17577step1 raw17577step1Labels := by
      have ha : raw17577step1 = raw17577step0 := by apply Matrix.ext; unfold raw17577step1 raw17577step0; decide +kernel
      have hl : raw17577step0Labels = labelEmbedding1 ∘ raw17577step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17577step0 raw17577step0Labels raw17577step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3520 node3520Labels := by rfl

def raw17578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17578Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17578step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17578step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17578step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17578 raw17578Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw17578 raw17578Labels = mixedMoment B raw17578step0 raw17578step0Labels := by
      have ha : raw17578step0 = (fun i j => raw17578 (permutation646 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17578step0 raw17578; decide +kernel
      have hl : raw17578step0Labels = raw17578Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17578 raw17578Labels permutation646 permutation7
    mixedMoment B raw17578step0 raw17578step0Labels = mixedMoment B raw17578step1 raw17578step1Labels := by
      have ha : raw17578step1 = raw17578step0 := by apply Matrix.ext; unfold raw17578step1 raw17578step0; decide +kernel
      have hl : raw17578step0Labels = labelEmbedding1 ∘ raw17578step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17578step0 raw17578step0Labels raw17578step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

def raw17579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw17579Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17579step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17579step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17579step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17579 raw17579Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw17579 raw17579Labels = mixedMoment B raw17579step0 raw17579step0Labels := by
      have ha : raw17579step0 = (fun i j => raw17579 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17579step0 raw17579; decide +kernel
      have hl : raw17579step0Labels = raw17579Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17579 raw17579Labels permutation644 permutation7
    mixedMoment B raw17579step0 raw17579step0Labels = mixedMoment B raw17579step1 raw17579step1Labels := by
      have ha : raw17579step1 = raw17579step0 := by apply Matrix.ext; unfold raw17579step1 raw17579step0; decide +kernel
      have hl : raw17579step0Labels = labelEmbedding1 ∘ raw17579step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17579step0 raw17579step0Labels raw17579step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

def raw17580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw17580Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw17580step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17580step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17580step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17580step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17580 raw17580Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw17580 raw17580Labels = mixedMoment B raw17580step0 raw17580step0Labels := by
      have hz : ∀ j, raw17580 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17580step0 = (fun i j => raw17580 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17580step0 raw17580; decide +kernel
      have hl : raw17580step0Labels = raw17580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17580 raw17580Labels permutation520 hz
    mixedMoment B raw17580step0 raw17580step0Labels = mixedMoment B raw17580step1 raw17580step1Labels := by
      have ha : raw17580step1 = (fun i j => raw17580step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17580step1 raw17580step0; decide +kernel
      have hl : raw17580step1Labels = raw17580step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17580step0 raw17580step0Labels permutation145 permutation7
    mixedMoment B raw17580step1 raw17580step1Labels = mixedMoment B raw17580step2 raw17580step2Labels := by
      have ha : raw17580step2 = raw17580step1 := by apply Matrix.ext; unfold raw17580step2 raw17580step1; decide +kernel
      have hl : raw17580step1Labels = labelEmbedding1 ∘ raw17580step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17580step1 raw17580step1Labels raw17580step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw17581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17581step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17581step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17581step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17581 raw17581Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw17581 raw17581Labels = mixedMoment B raw17581step0 raw17581step0Labels := by
      have ha : raw17581step0 = (fun i j => raw17581 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17581step0 raw17581; decide +kernel
      have hl : raw17581step0Labels = raw17581Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17581 raw17581Labels permutation271 permutation3
    mixedMoment B raw17581step0 raw17581step0Labels = mixedMoment B raw17581step1 raw17581step1Labels := by
      have ha : raw17581step1 = raw17581step0 := by apply Matrix.ext; unfold raw17581step1 raw17581step0; decide +kernel
      have hl : raw17581step0Labels = labelEmbedding6 ∘ raw17581step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17581step0 raw17581step0Labels raw17581step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5423 node5423Labels := by rfl

def raw17582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17582step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17582step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17582step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17582step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17582step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17582 raw17582Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw17582 raw17582Labels = mixedMoment B raw17582step0 raw17582step0Labels := by
      have ha : raw17582step0 = (fun i j => raw17582 (permutation684 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17582step0 raw17582; decide +kernel
      have hl : raw17582step0Labels = raw17582Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17582 raw17582Labels permutation684 permutation3
    mixedMoment B raw17582step0 raw17582step0Labels = mixedMoment B raw17582step1 raw17582step1Labels := by
      have ha : raw17582step1 = -raw17582step0 := by apply Matrix.ext; change ∀ i j, raw17582step1 i j = -(raw17582step0 i j); unfold raw17582step1 raw17582step0; decide +kernel
      have hl : raw17582step1Labels = raw17582step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17582step1 raw17582step1Labels = mixedMoment B raw17582step2 raw17582step2Labels := by
      have ha : raw17582step2 = raw17582step1 := by apply Matrix.ext; unfold raw17582step2 raw17582step1; decide +kernel
      have hl : raw17582step1Labels = labelEmbedding6 ∘ raw17582step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17582step1 raw17582step1Labels raw17582step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw17583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17583step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17583step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17583step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17583 raw17583Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17583 raw17583Labels = mixedMoment B raw17583step0 raw17583step0Labels := by
      have ha : raw17583step0 = (fun i j => raw17583 (permutation641 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17583step0 raw17583; decide +kernel
      have hl : raw17583step0Labels = raw17583Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17583 raw17583Labels permutation641 permutation5
    mixedMoment B raw17583step0 raw17583step0Labels = mixedMoment B raw17583step1 raw17583step1Labels := by
      have ha : raw17583step1 = raw17583step0 := by apply Matrix.ext; unfold raw17583step1 raw17583step0; decide +kernel
      have hl : raw17583step0Labels = labelEmbedding8 ∘ raw17583step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17583step0 raw17583step0Labels raw17583step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw17584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17584step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17584step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17584 raw17584Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw17584 raw17584Labels = mixedMoment B raw17584step0 raw17584step0Labels := by
      have ha : raw17584step0 = (fun i j => raw17584 (permutation626 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17584step0 raw17584; decide +kernel
      have hl : raw17584step0Labels = raw17584Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17584 raw17584Labels permutation626 permutation5
    mixedMoment B raw17584step0 raw17584step0Labels = mixedMoment B raw17584step1 raw17584step1Labels := by
      have ha : raw17584step1 = raw17584step0 := by apply Matrix.ext; unfold raw17584step1 raw17584step0; decide +kernel
      have hl : raw17584step0Labels = labelEmbedding8 ∘ raw17584step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17584step0 raw17584step0Labels raw17584step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw17585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw17585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17585step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17585 raw17585Labels = mixedMoment B node5500 node5500Labels := by
  calc
    mixedMoment B raw17585 raw17585Labels = mixedMoment B raw17585step0 raw17585step0Labels := by
      have ha : raw17585step0 = (fun i j => raw17585 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17585step0 raw17585; decide +kernel
      have hl : raw17585step0Labels = raw17585Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17585 raw17585Labels permutation153 permutation2
    _ = mixedMoment B node5500 node5500Labels := by rfl

def raw17586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17586step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17586step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17586step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17586step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17586step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17586step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17586 raw17586Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw17586 raw17586Labels = mixedMoment B raw17586step0 raw17586step0Labels := by
      have hz : ∀ j, raw17586 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw17586step0 = (fun i j => raw17586 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw17586step0 raw17586; decide +kernel
      have hl : raw17586step0Labels = raw17586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17586 raw17586Labels permutation265 hz
    mixedMoment B raw17586step0 raw17586step0Labels = mixedMoment B raw17586step1 raw17586step1Labels := by
      have ha : raw17586step1 = (fun i j => raw17586step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17586step1 raw17586step0; decide +kernel
      have hl : raw17586step1Labels = raw17586step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17586step0 raw17586step0Labels permutation151 permutation3
    mixedMoment B raw17586step1 raw17586step1Labels = mixedMoment B raw17586step2 raw17586step2Labels := by
      have ha : raw17586step2 = -raw17586step1 := by apply Matrix.ext; change ∀ i j, raw17586step2 i j = -(raw17586step1 i j); unfold raw17586step2 raw17586step1; decide +kernel
      have hl : raw17586step2Labels = raw17586step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17586step2 raw17586step2Labels = mixedMoment B raw17586step3 raw17586step3Labels := by
      have ha : raw17586step3 = raw17586step2 := by apply Matrix.ext; unfold raw17586step3 raw17586step2; decide +kernel
      have hl : raw17586step2Labels = labelEmbedding6 ∘ raw17586step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17586step2 raw17586step2Labels raw17586step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw17587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17587step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17587step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17587step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17587step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17587step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17587 raw17587Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw17587 raw17587Labels = mixedMoment B raw17587step0 raw17587step0Labels := by
      have hz : ∀ j, raw17587 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw17587step0 = (fun i j => raw17587 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw17587step0 raw17587; decide +kernel
      have hl : raw17587step0Labels = raw17587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17587 raw17587Labels permutation265 hz
    mixedMoment B raw17587step0 raw17587step0Labels = mixedMoment B raw17587step1 raw17587step1Labels := by
      have ha : raw17587step1 = (fun i j => raw17587step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17587step1 raw17587step0; decide +kernel
      have hl : raw17587step1Labels = raw17587step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17587step0 raw17587step0Labels permutation149 permutation3
    mixedMoment B raw17587step1 raw17587step1Labels = mixedMoment B raw17587step2 raw17587step2Labels := by
      have ha : raw17587step2 = -raw17587step1 := by apply Matrix.ext; change ∀ i j, raw17587step2 i j = -(raw17587step1 i j); unfold raw17587step2 raw17587step1; decide +kernel
      have hl : raw17587step2Labels = raw17587step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17587step2 raw17587step2Labels = mixedMoment B raw17587step3 raw17587step3Labels := by
      have ha : raw17587step3 = raw17587step2 := by apply Matrix.ext; unfold raw17587step3 raw17587step2; decide +kernel
      have hl : raw17587step2Labels = labelEmbedding6 ∘ raw17587step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17587step2 raw17587step2Labels raw17587step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw17588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17588step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17588step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17588step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17588 raw17588Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw17588 raw17588Labels = mixedMoment B raw17588step0 raw17588step0Labels := by
      have hz : ∀ j, raw17588 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw17588step0 = (fun i j => raw17588 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw17588step0 raw17588; decide +kernel
      have hl : raw17588step0Labels = raw17588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17588 raw17588Labels permutation265 hz
    mixedMoment B raw17588step0 raw17588step0Labels = mixedMoment B raw17588step1 raw17588step1Labels := by
      have ha : raw17588step1 = (fun i j => raw17588step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17588step1 raw17588step0; decide +kernel
      have hl : raw17588step1Labels = raw17588step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17588step0 raw17588step0Labels permutation137 permutation5
    mixedMoment B raw17588step1 raw17588step1Labels = mixedMoment B raw17588step2 raw17588step2Labels := by
      have ha : raw17588step2 = raw17588step1 := by apply Matrix.ext; unfold raw17588step2 raw17588step1; decide +kernel
      have hl : raw17588step1Labels = labelEmbedding8 ∘ raw17588step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17588step1 raw17588step1Labels raw17588step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw17589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17589step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17589step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17589step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17589 raw17589Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw17589 raw17589Labels = mixedMoment B raw17589step0 raw17589step0Labels := by
      have ha : raw17589step0 = (fun i j => raw17589 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17589step0 raw17589; decide +kernel
      have hl : raw17589step0Labels = raw17589Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17589 raw17589Labels permutation160 permutation3
    mixedMoment B raw17589step0 raw17589step0Labels = mixedMoment B raw17589step1 raw17589step1Labels := by
      have ha : raw17589step1 = raw17589step0 := by apply Matrix.ext; unfold raw17589step1 raw17589step0; decide +kernel
      have hl : raw17589step0Labels = labelEmbedding6 ∘ raw17589step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17589step0 raw17589step0Labels raw17589step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

def raw17590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17590step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17590step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17590step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17590 raw17590Labels = mixedMoment B node5344 node5344Labels := by
  calc
    mixedMoment B raw17590 raw17590Labels = mixedMoment B raw17590step0 raw17590step0Labels := by
      have ha : raw17590step0 = (fun i j => raw17590 (permutation273 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17590step0 raw17590; decide +kernel
      have hl : raw17590step0Labels = raw17590Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17590 raw17590Labels permutation273 permutation3
    mixedMoment B raw17590step0 raw17590step0Labels = mixedMoment B raw17590step1 raw17590step1Labels := by
      have ha : raw17590step1 = raw17590step0 := by apply Matrix.ext; unfold raw17590step1 raw17590step0; decide +kernel
      have hl : raw17590step0Labels = labelEmbedding6 ∘ raw17590step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17590step0 raw17590step0Labels raw17590step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5344 node5344Labels := by rfl

def raw17591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17591step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17591step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17591step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17591 raw17591Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw17591 raw17591Labels = mixedMoment B raw17591step0 raw17591step0Labels := by
      have ha : raw17591step0 = (fun i j => raw17591 (permutation643 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17591step0 raw17591; decide +kernel
      have hl : raw17591step0Labels = raw17591Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17591 raw17591Labels permutation643 permutation5
    mixedMoment B raw17591step0 raw17591step0Labels = mixedMoment B raw17591step1 raw17591step1Labels := by
      have ha : raw17591step1 = raw17591step0 := by apply Matrix.ext; unfold raw17591step1 raw17591step0; decide +kernel
      have hl : raw17591step0Labels = labelEmbedding8 ∘ raw17591step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17591step0 raw17591step0Labels raw17591step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

def raw17592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17592step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17592step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17592step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17592 raw17592Labels = mixedMoment B node5365 node5365Labels := by
  calc
    mixedMoment B raw17592 raw17592Labels = mixedMoment B raw17592step0 raw17592step0Labels := by
      have ha : raw17592step0 = (fun i j => raw17592 (permutation640 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17592step0 raw17592; decide +kernel
      have hl : raw17592step0Labels = raw17592Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17592 raw17592Labels permutation640 permutation5
    mixedMoment B raw17592step0 raw17592step0Labels = mixedMoment B raw17592step1 raw17592step1Labels := by
      have ha : raw17592step1 = raw17592step0 := by apply Matrix.ext; unfold raw17592step1 raw17592step0; decide +kernel
      have hl : raw17592step0Labels = labelEmbedding8 ∘ raw17592step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17592step0 raw17592step0Labels raw17592step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5365 node5365Labels := by rfl

def raw17593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw17593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17593step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17593step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17593step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17593 raw17593Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw17593 raw17593Labels = mixedMoment B raw17593step0 raw17593step0Labels := by
      have ha : raw17593step0 = (fun i j => raw17593 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17593step0 raw17593; decide +kernel
      have hl : raw17593step0Labels = raw17593Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17593 raw17593Labels permutation161 permutation3
    mixedMoment B raw17593step0 raw17593step0Labels = mixedMoment B raw17593step1 raw17593step1Labels := by
      have ha : raw17593step1 = raw17593step0 := by apply Matrix.ext; unfold raw17593step1 raw17593step0; decide +kernel
      have hl : raw17593step0Labels = labelEmbedding6 ∘ raw17593step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17593step0 raw17593step0Labels raw17593step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw17594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17594step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17594step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17594step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17594 raw17594Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw17594 raw17594Labels = mixedMoment B raw17594step0 raw17594step0Labels := by
      have ha : raw17594step0 = (fun i j => raw17594 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17594step0 raw17594; decide +kernel
      have hl : raw17594step0Labels = raw17594Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17594 raw17594Labels permutation265 permutation3
    mixedMoment B raw17594step0 raw17594step0Labels = mixedMoment B raw17594step1 raw17594step1Labels := by
      have ha : raw17594step1 = raw17594step0 := by apply Matrix.ext; unfold raw17594step1 raw17594step0; decide +kernel
      have hl : raw17594step0Labels = labelEmbedding6 ∘ raw17594step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17594step0 raw17594step0Labels raw17594step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

def raw17595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17595step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17595step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17595step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17595step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17595step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17595 raw17595Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw17595 raw17595Labels = mixedMoment B raw17595step0 raw17595step0Labels := by
      have ha : raw17595step0 = (fun i j => raw17595 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17595step0 raw17595; decide +kernel
      have hl : raw17595step0Labels = raw17595Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17595 raw17595Labels permutation664 permutation3
    mixedMoment B raw17595step0 raw17595step0Labels = mixedMoment B raw17595step1 raw17595step1Labels := by
      have ha : raw17595step1 = -raw17595step0 := by apply Matrix.ext; change ∀ i j, raw17595step1 i j = -(raw17595step0 i j); unfold raw17595step1 raw17595step0; decide +kernel
      have hl : raw17595step1Labels = raw17595step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17595step1 raw17595step1Labels = mixedMoment B raw17595step2 raw17595step2Labels := by
      have ha : raw17595step2 = raw17595step1 := by apply Matrix.ext; unfold raw17595step2 raw17595step1; decide +kernel
      have hl : raw17595step1Labels = labelEmbedding6 ∘ raw17595step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17595step1 raw17595step1Labels raw17595step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5416 node5416Labels := by rfl

def raw17596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17596step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17596step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17596step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17596step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17596step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17596 raw17596Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17596 raw17596Labels = mixedMoment B raw17596step0 raw17596step0Labels := by
      have ha : raw17596step0 = (fun i j => raw17596 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17596step0 raw17596; decide +kernel
      have hl : raw17596step0Labels = raw17596Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17596 raw17596Labels permutation658 permutation3
    mixedMoment B raw17596step0 raw17596step0Labels = mixedMoment B raw17596step1 raw17596step1Labels := by
      have ha : raw17596step1 = -raw17596step0 := by apply Matrix.ext; change ∀ i j, raw17596step1 i j = -(raw17596step0 i j); unfold raw17596step1 raw17596step0; decide +kernel
      have hl : raw17596step1Labels = raw17596step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17596step1 raw17596step1Labels = mixedMoment B raw17596step2 raw17596step2Labels := by
      have ha : raw17596step2 = raw17596step1 := by apply Matrix.ext; unfold raw17596step2 raw17596step1; decide +kernel
      have hl : raw17596step1Labels = labelEmbedding6 ∘ raw17596step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17596step1 raw17596step1Labels raw17596step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw17597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17597step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17597step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17597step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17597 raw17597Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw17597 raw17597Labels = mixedMoment B raw17597step0 raw17597step0Labels := by
      have ha : raw17597step0 = (fun i j => raw17597 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17597step0 raw17597; decide +kernel
      have hl : raw17597step0Labels = raw17597Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17597 raw17597Labels permutation158 permutation3
    mixedMoment B raw17597step0 raw17597step0Labels = mixedMoment B raw17597step1 raw17597step1Labels := by
      have ha : raw17597step1 = raw17597step0 := by apply Matrix.ext; unfold raw17597step1 raw17597step0; decide +kernel
      have hl : raw17597step0Labels = labelEmbedding6 ∘ raw17597step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17597step0 raw17597step0Labels raw17597step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5050 node5050Labels := by rfl

def raw17598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17598step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17598step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17598step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17598 raw17598Labels = mixedMoment B node5341 node5341Labels := by
  calc
    mixedMoment B raw17598 raw17598Labels = mixedMoment B raw17598step0 raw17598step0Labels := by
      have ha : raw17598step0 = (fun i j => raw17598 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17598step0 raw17598; decide +kernel
      have hl : raw17598step0Labels = raw17598Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17598 raw17598Labels permutation271 permutation3
    mixedMoment B raw17598step0 raw17598step0Labels = mixedMoment B raw17598step1 raw17598step1Labels := by
      have ha : raw17598step1 = raw17598step0 := by apply Matrix.ext; unfold raw17598step1 raw17598step0; decide +kernel
      have hl : raw17598step0Labels = labelEmbedding6 ∘ raw17598step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17598step0 raw17598step0Labels raw17598step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5341 node5341Labels := by rfl

def raw17599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17599step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17599step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17599step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17599step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17599step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17599 raw17599Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw17599 raw17599Labels = mixedMoment B raw17599step0 raw17599step0Labels := by
      have ha : raw17599step0 = (fun i j => raw17599 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17599step0 raw17599; decide +kernel
      have hl : raw17599step0Labels = raw17599Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17599 raw17599Labels permutation688 permutation3
    mixedMoment B raw17599step0 raw17599step0Labels = mixedMoment B raw17599step1 raw17599step1Labels := by
      have ha : raw17599step1 = -raw17599step0 := by apply Matrix.ext; change ∀ i j, raw17599step1 i j = -(raw17599step0 i j); unfold raw17599step1 raw17599step0; decide +kernel
      have hl : raw17599step1Labels = raw17599step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17599step1 raw17599step1Labels = mixedMoment B raw17599step2 raw17599step2Labels := by
      have ha : raw17599step2 = raw17599step1 := by apply Matrix.ext; unfold raw17599step2 raw17599step1; decide +kernel
      have hl : raw17599step1Labels = labelEmbedding6 ∘ raw17599step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17599step1 raw17599step1Labels raw17599step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw17600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17600step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17600step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17600step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17600step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17600 raw17600Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw17600 raw17600Labels = mixedMoment B raw17600step0 raw17600step0Labels := by
      have ha : raw17600step0 = (fun i j => raw17600 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17600step0 raw17600; decide +kernel
      have hl : raw17600step0Labels = raw17600Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17600 raw17600Labels permutation680 permutation3
    mixedMoment B raw17600step0 raw17600step0Labels = mixedMoment B raw17600step1 raw17600step1Labels := by
      have ha : raw17600step1 = -raw17600step0 := by apply Matrix.ext; change ∀ i j, raw17600step1 i j = -(raw17600step0 i j); unfold raw17600step1 raw17600step0; decide +kernel
      have hl : raw17600step1Labels = raw17600step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17600step1 raw17600step1Labels = mixedMoment B raw17600step2 raw17600step2Labels := by
      have ha : raw17600step2 = raw17600step1 := by apply Matrix.ext; unfold raw17600step2 raw17600step1; decide +kernel
      have hl : raw17600step1Labels = labelEmbedding6 ∘ raw17600step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17600step1 raw17600step1Labels raw17600step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

def raw17601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw17601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17601step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17601step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17601step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17601 raw17601Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw17601 raw17601Labels = mixedMoment B raw17601step0 raw17601step0Labels := by
      have ha : raw17601step0 = (fun i j => raw17601 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17601step0 raw17601; decide +kernel
      have hl : raw17601step0Labels = raw17601Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17601 raw17601Labels permutation159 permutation3
    mixedMoment B raw17601step0 raw17601step0Labels = mixedMoment B raw17601step1 raw17601step1Labels := by
      have ha : raw17601step1 = raw17601step0 := by apply Matrix.ext; unfold raw17601step1 raw17601step0; decide +kernel
      have hl : raw17601step0Labels = labelEmbedding6 ∘ raw17601step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17601step0 raw17601step0Labels raw17601step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

def raw17602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw17602step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw17602step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17602step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw17602step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17602 raw17602Labels = mixedMoment B node4779 node4779Labels := by
  calc
    mixedMoment B raw17602 raw17602Labels = mixedMoment B raw17602step0 raw17602step0Labels := by
      have ha : raw17602step0 = (fun i j => raw17602 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17602step0 raw17602; decide +kernel
      have hl : raw17602step0Labels = raw17602Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17602 raw17602Labels permutation682 permutation3
    mixedMoment B raw17602step0 raw17602step0Labels = mixedMoment B raw17602step1 raw17602step1Labels := by
      have ha : raw17602step1 = -raw17602step0 := by apply Matrix.ext; change ∀ i j, raw17602step1 i j = -(raw17602step0 i j); unfold raw17602step1 raw17602step0; decide +kernel
      have hl : raw17602step1Labels = raw17602step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17602step1 raw17602step1Labels = mixedMoment B raw17602step2 raw17602step2Labels := by
      have ha : raw17602step2 = raw17602step1 := by apply Matrix.ext; unfold raw17602step2 raw17602step1; decide +kernel
      have hl : raw17602step1Labels = labelEmbedding6 ∘ raw17602step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17602step1 raw17602step1Labels raw17602step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4779 node4779Labels := by rfl

def raw17603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17603step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17603step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17603step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17603step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17603 raw17603Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw17603 raw17603Labels = mixedMoment B raw17603step0 raw17603step0Labels := by
      have ha : raw17603step0 = (fun i j => raw17603 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17603step0 raw17603; decide +kernel
      have hl : raw17603step0Labels = raw17603Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17603 raw17603Labels permutation681 permutation3
    mixedMoment B raw17603step0 raw17603step0Labels = mixedMoment B raw17603step1 raw17603step1Labels := by
      have ha : raw17603step1 = -raw17603step0 := by apply Matrix.ext; change ∀ i j, raw17603step1 i j = -(raw17603step0 i j); unfold raw17603step1 raw17603step0; decide +kernel
      have hl : raw17603step1Labels = raw17603step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17603step1 raw17603step1Labels = mixedMoment B raw17603step2 raw17603step2Labels := by
      have ha : raw17603step2 = raw17603step1 := by apply Matrix.ext; unfold raw17603step2 raw17603step1; decide +kernel
      have hl : raw17603step1Labels = labelEmbedding6 ∘ raw17603step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17603step1 raw17603step1Labels raw17603step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

def raw17604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17604step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17604step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17604step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17604step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17604 raw17604Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw17604 raw17604Labels = mixedMoment B raw17604step0 raw17604step0Labels := by
      have ha : raw17604step0 = (fun i j => raw17604 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17604step0 raw17604; decide +kernel
      have hl : raw17604step0Labels = raw17604Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17604 raw17604Labels permutation688 permutation3
    mixedMoment B raw17604step0 raw17604step0Labels = mixedMoment B raw17604step1 raw17604step1Labels := by
      have ha : raw17604step1 = -raw17604step0 := by apply Matrix.ext; change ∀ i j, raw17604step1 i j = -(raw17604step0 i j); unfold raw17604step1 raw17604step0; decide +kernel
      have hl : raw17604step1Labels = raw17604step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17604step1 raw17604step1Labels = mixedMoment B raw17604step2 raw17604step2Labels := by
      have ha : raw17604step2 = raw17604step1 := by apply Matrix.ext; unfold raw17604step2 raw17604step1; decide +kernel
      have hl : raw17604step1Labels = labelEmbedding6 ∘ raw17604step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17604step1 raw17604step1Labels raw17604step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw17605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17605step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17605step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17605step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17605step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17605 raw17605Labels = mixedMoment B node4787 node4787Labels := by
  calc
    mixedMoment B raw17605 raw17605Labels = mixedMoment B raw17605step0 raw17605step0Labels := by
      have ha : raw17605step0 = (fun i j => raw17605 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17605step0 raw17605; decide +kernel
      have hl : raw17605step0Labels = raw17605Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17605 raw17605Labels permutation680 permutation3
    mixedMoment B raw17605step0 raw17605step0Labels = mixedMoment B raw17605step1 raw17605step1Labels := by
      have ha : raw17605step1 = -raw17605step0 := by apply Matrix.ext; change ∀ i j, raw17605step1 i j = -(raw17605step0 i j); unfold raw17605step1 raw17605step0; decide +kernel
      have hl : raw17605step1Labels = raw17605step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17605step1 raw17605step1Labels = mixedMoment B raw17605step2 raw17605step2Labels := by
      have ha : raw17605step2 = raw17605step1 := by apply Matrix.ext; unfold raw17605step2 raw17605step1; decide +kernel
      have hl : raw17605step1Labels = labelEmbedding6 ∘ raw17605step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17605step1 raw17605step1Labels raw17605step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4787 node4787Labels := by rfl

def raw17606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw17606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17606step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17606step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17606 raw17606Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw17606 raw17606Labels = mixedMoment B raw17606step0 raw17606step0Labels := by
      have ha : raw17606step0 = (fun i j => raw17606 (permutation640 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17606step0 raw17606; decide +kernel
      have hl : raw17606step0Labels = raw17606Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17606 raw17606Labels permutation640 permutation5
    mixedMoment B raw17606step0 raw17606step0Labels = mixedMoment B raw17606step1 raw17606step1Labels := by
      have ha : raw17606step1 = raw17606step0 := by apply Matrix.ext; unfold raw17606step1 raw17606step0; decide +kernel
      have hl : raw17606step0Labels = labelEmbedding8 ∘ raw17606step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17606step0 raw17606step0Labels raw17606step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

def raw17607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17607Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17607step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17607 raw17607Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw17607 raw17607Labels = mixedMoment B raw17607step0 raw17607step0Labels := by
      have ha : raw17607step0 = (fun i j => raw17607 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17607step0 raw17607; decide +kernel
      have hl : raw17607step0Labels = raw17607Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17607 raw17607Labels permutation271 permutation3
    _ = mixedMoment B node3837 node3837Labels := by rfl

def raw17608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17608Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17608step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17608step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17608step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17608 raw17608Labels = mixedMoment B node3851 node3851Labels := by
  calc
    mixedMoment B raw17608 raw17608Labels = mixedMoment B raw17608step0 raw17608step0Labels := by
      have ha : raw17608step0 = (fun i j => raw17608 (permutation684 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17608step0 raw17608; decide +kernel
      have hl : raw17608step0Labels = raw17608Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17608 raw17608Labels permutation684 permutation3
    mixedMoment B raw17608step0 raw17608step0Labels = mixedMoment B raw17608step1 raw17608step1Labels := by
      have ha : raw17608step1 = -raw17608step0 := by apply Matrix.ext; change ∀ i j, raw17608step1 i j = -(raw17608step0 i j); unfold raw17608step1 raw17608step0; decide +kernel
      have hl : raw17608step1Labels = raw17608step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3851 node3851Labels := by rfl

def raw17609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17609Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17609step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17609step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17609 raw17609Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw17609 raw17609Labels = mixedMoment B raw17609step0 raw17609step0Labels := by
      have ha : raw17609step0 = (fun i j => raw17609 (permutation677 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17609step0 raw17609; decide +kernel
      have hl : raw17609step0Labels = raw17609Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17609 raw17609Labels permutation677 permutation3
    mixedMoment B raw17609step0 raw17609step0Labels = mixedMoment B raw17609step1 raw17609step1Labels := by
      have ha : raw17609step1 = -raw17609step0 := by apply Matrix.ext; change ∀ i j, raw17609step1 i j = -(raw17609step0 i j); unfold raw17609step1 raw17609step0; decide +kernel
      have hl : raw17609step1Labels = raw17609step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw17610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17610Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17610step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17610step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17610step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17610 raw17610Labels = mixedMoment B node3901 node3901Labels := by
  calc
    mixedMoment B raw17610 raw17610Labels = mixedMoment B raw17610step0 raw17610step0Labels := by
      have ha : raw17610step0 = (fun i j => raw17610 (permutation639 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17610step0 raw17610; decide +kernel
      have hl : raw17610step0Labels = raw17610Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17610 raw17610Labels permutation639 permutation3
    mixedMoment B raw17610step0 raw17610step0Labels = mixedMoment B raw17610step1 raw17610step1Labels := by
      have ha : raw17610step1 = -raw17610step0 := by apply Matrix.ext; change ∀ i j, raw17610step1 i j = -(raw17610step0 i j); unfold raw17610step1 raw17610step0; decide +kernel
      have hl : raw17610step1Labels = raw17610step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3901 node3901Labels := by rfl

def raw17611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw17611Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17611step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17611 raw17611Labels = mixedMoment B node4053 node4053Labels := by
  calc
    mixedMoment B raw17611 raw17611Labels = mixedMoment B raw17611step0 raw17611step0Labels := by
      have ha : raw17611step0 = (fun i j => raw17611 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17611step0 raw17611; decide +kernel
      have hl : raw17611step0Labels = raw17611Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17611 raw17611Labels permutation271 permutation3
    _ = mixedMoment B node4053 node4053Labels := by rfl

def raw17612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17612Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17612step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17612step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17612 raw17612Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw17612 raw17612Labels = mixedMoment B raw17612step0 raw17612step0Labels := by
      have hz : ∀ j, raw17612 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw17612step0 = (fun i j => raw17612 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw17612step0 raw17612; decide +kernel
      have hl : raw17612step0Labels = raw17612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17612 raw17612Labels permutation265 hz
    mixedMoment B raw17612step0 raw17612step0Labels = mixedMoment B raw17612step1 raw17612step1Labels := by
      have ha : raw17612step1 = (fun i j => raw17612step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17612step1 raw17612step0; decide +kernel
      have hl : raw17612step1Labels = raw17612step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17612step0 raw17612step0Labels permutation151 permutation3
    mixedMoment B raw17612step1 raw17612step1Labels = mixedMoment B raw17612step2 raw17612step2Labels := by
      have ha : raw17612step2 = -raw17612step1 := by apply Matrix.ext; change ∀ i j, raw17612step2 i j = -(raw17612step1 i j); unfold raw17612step2 raw17612step1; decide +kernel
      have hl : raw17612step2Labels = raw17612step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw17613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17613Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17613step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17613step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17613step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17613step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17613 raw17613Labels = mixedMoment B node3845 node3845Labels := by
  calc
    mixedMoment B raw17613 raw17613Labels = mixedMoment B raw17613step0 raw17613step0Labels := by
      have hz : ∀ j, raw17613 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw17613step0 = (fun i j => raw17613 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw17613step0 raw17613; decide +kernel
      have hl : raw17613step0Labels = raw17613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17613 raw17613Labels permutation265 hz
    mixedMoment B raw17613step0 raw17613step0Labels = mixedMoment B raw17613step1 raw17613step1Labels := by
      have ha : raw17613step1 = (fun i j => raw17613step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17613step1 raw17613step0; decide +kernel
      have hl : raw17613step1Labels = raw17613step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17613step0 raw17613step0Labels permutation149 permutation3
    mixedMoment B raw17613step1 raw17613step1Labels = mixedMoment B raw17613step2 raw17613step2Labels := by
      have ha : raw17613step2 = -raw17613step1 := by apply Matrix.ext; change ∀ i j, raw17613step2 i j = -(raw17613step1 i j); unfold raw17613step2 raw17613step1; decide +kernel
      have hl : raw17613step2Labels = raw17613step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3845 node3845Labels := by rfl

def raw17614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17614Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17614step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw17614step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw17614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17614 raw17614Labels = mixedMoment B node3902 node3902Labels := by
  calc
    mixedMoment B raw17614 raw17614Labels = mixedMoment B raw17614step0 raw17614step0Labels := by
      have hz : ∀ j, raw17614 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw17614step0 = (fun i j => raw17614 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw17614step0 raw17614; decide +kernel
      have hl : raw17614step0Labels = raw17614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17614 raw17614Labels permutation265 hz
    mixedMoment B raw17614step0 raw17614step0Labels = mixedMoment B raw17614step1 raw17614step1Labels := by
      have ha : raw17614step1 = (fun i j => raw17614step0 (permutation137 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17614step1 raw17614step0; decide +kernel
      have hl : raw17614step1Labels = raw17614step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17614step0 raw17614step0Labels permutation137 permutation3
    mixedMoment B raw17614step1 raw17614step1Labels = mixedMoment B raw17614step2 raw17614step2Labels := by
      have ha : raw17614step2 = -raw17614step1 := by apply Matrix.ext; change ∀ i j, raw17614step2 i j = -(raw17614step1 i j); unfold raw17614step2 raw17614step1; decide +kernel
      have hl : raw17614step2Labels = raw17614step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3902 node3902Labels := by rfl

def raw17615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17615Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17615step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17615 raw17615Labels = mixedMoment B node2459 node2459Labels := by
  calc
    mixedMoment B raw17615 raw17615Labels = mixedMoment B raw17615step0 raw17615step0Labels := by
      have ha : raw17615step0 = (fun i j => raw17615 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17615step0 raw17615; decide +kernel
      have hl : raw17615step0Labels = raw17615Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17615 raw17615Labels permutation160 permutation3
    _ = mixedMoment B node2459 node2459Labels := by rfl

def raw17616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17616Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw17616step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17616 raw17616Labels = mixedMoment B node3681 node3681Labels := by
  calc
    mixedMoment B raw17616 raw17616Labels = mixedMoment B raw17616step0 raw17616step0Labels := by
      have ha : raw17616step0 = (fun i j => raw17616 (permutation273 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17616step0 raw17616; decide +kernel
      have hl : raw17616step0Labels = raw17616Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17616 raw17616Labels permutation273 permutation3
    _ = mixedMoment B node3681 node3681Labels := by rfl

def raw17617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17617Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17617step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17617step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17617step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17617 raw17617Labels = mixedMoment B node3746 node3746Labels := by
  calc
    mixedMoment B raw17617 raw17617Labels = mixedMoment B raw17617step0 raw17617step0Labels := by
      have ha : raw17617step0 = (fun i j => raw17617 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17617step0 raw17617; decide +kernel
      have hl : raw17617step0Labels = raw17617Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17617 raw17617Labels permutation644 permutation3
    mixedMoment B raw17617step0 raw17617step0Labels = mixedMoment B raw17617step1 raw17617step1Labels := by
      have ha : raw17617step1 = -raw17617step0 := by apply Matrix.ext; change ∀ i j, raw17617step1 i j = -(raw17617step0 i j); unfold raw17617step1 raw17617step0; decide +kernel
      have hl : raw17617step1Labels = raw17617step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3746 node3746Labels := by rfl

def raw17618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17618Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17618step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17618step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17618 raw17618Labels = mixedMoment B node3758 node3758Labels := by
  calc
    mixedMoment B raw17618 raw17618Labels = mixedMoment B raw17618step0 raw17618step0Labels := by
      have ha : raw17618step0 = (fun i j => raw17618 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17618step0 raw17618; decide +kernel
      have hl : raw17618step0Labels = raw17618Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17618 raw17618Labels permutation640 permutation3
    mixedMoment B raw17618step0 raw17618step0Labels = mixedMoment B raw17618step1 raw17618step1Labels := by
      have ha : raw17618step1 = -raw17618step0 := by apply Matrix.ext; change ∀ i j, raw17618step1 i j = -(raw17618step0 i j); unfold raw17618step1 raw17618step0; decide +kernel
      have hl : raw17618step1Labels = raw17618step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3758 node3758Labels := by rfl

def raw17619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw17619Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17619step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17619 raw17619Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw17619 raw17619Labels = mixedMoment B raw17619step0 raw17619step0Labels := by
      have ha : raw17619step0 = (fun i j => raw17619 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17619step0 raw17619; decide +kernel
      have hl : raw17619step0Labels = raw17619Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17619 raw17619Labels permutation161 permutation3
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw17620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17620Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw17620step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17620 raw17620Labels = mixedMoment B node3689 node3689Labels := by
  calc
    mixedMoment B raw17620 raw17620Labels = mixedMoment B raw17620step0 raw17620step0Labels := by
      have ha : raw17620step0 = (fun i j => raw17620 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17620step0 raw17620; decide +kernel
      have hl : raw17620step0Labels = raw17620Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17620 raw17620Labels permutation265 permutation3
    _ = mixedMoment B node3689 node3689Labels := by rfl

def raw17621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17621Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17621step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17621step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17621step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17621 raw17621Labels = mixedMoment B node3821 node3821Labels := by
  calc
    mixedMoment B raw17621 raw17621Labels = mixedMoment B raw17621step0 raw17621step0Labels := by
      have ha : raw17621step0 = (fun i j => raw17621 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17621step0 raw17621; decide +kernel
      have hl : raw17621step0Labels = raw17621Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17621 raw17621Labels permutation664 permutation3
    mixedMoment B raw17621step0 raw17621step0Labels = mixedMoment B raw17621step1 raw17621step1Labels := by
      have ha : raw17621step1 = -raw17621step0 := by apply Matrix.ext; change ∀ i j, raw17621step1 i j = -(raw17621step0 i j); unfold raw17621step1 raw17621step0; decide +kernel
      have hl : raw17621step1Labels = raw17621step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3821 node3821Labels := by rfl

def raw17622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw17622Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17622step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17622step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17622step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17622 raw17622Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw17622 raw17622Labels = mixedMoment B raw17622step0 raw17622step0Labels := by
      have ha : raw17622step0 = (fun i j => raw17622 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17622step0 raw17622; decide +kernel
      have hl : raw17622step0Labels = raw17622Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17622 raw17622Labels permutation658 permutation3
    mixedMoment B raw17622step0 raw17622step0Labels = mixedMoment B raw17622step1 raw17622step1Labels := by
      have ha : raw17622step1 = -raw17622step0 := by apply Matrix.ext; change ∀ i j, raw17622step1 i j = -(raw17622step0 i j); unfold raw17622step1 raw17622step0; decide +kernel
      have hl : raw17622step1Labels = raw17622step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw17623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17623Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17623step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17623 raw17623Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw17623 raw17623Labels = mixedMoment B raw17623step0 raw17623step0Labels := by
      have ha : raw17623step0 = (fun i j => raw17623 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17623step0 raw17623; decide +kernel
      have hl : raw17623step0Labels = raw17623Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17623 raw17623Labels permutation158 permutation3
    _ = mixedMoment B node2452 node2452Labels := by rfl

def raw17624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17624Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17624step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17624 raw17624Labels = mixedMoment B node3678 node3678Labels := by
  calc
    mixedMoment B raw17624 raw17624Labels = mixedMoment B raw17624step0 raw17624step0Labels := by
      have ha : raw17624step0 = (fun i j => raw17624 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17624step0 raw17624; decide +kernel
      have hl : raw17624step0Labels = raw17624Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17624 raw17624Labels permutation271 permutation3
    _ = mixedMoment B node3678 node3678Labels := by rfl

def raw17625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17625Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17625step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17625step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17625step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17625 raw17625Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw17625 raw17625Labels = mixedMoment B raw17625step0 raw17625step0Labels := by
      have ha : raw17625step0 = (fun i j => raw17625 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17625step0 raw17625; decide +kernel
      have hl : raw17625step0Labels = raw17625Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17625 raw17625Labels permutation688 permutation3
    mixedMoment B raw17625step0 raw17625step0Labels = mixedMoment B raw17625step1 raw17625step1Labels := by
      have ha : raw17625step1 = -raw17625step0 := by apply Matrix.ext; change ∀ i j, raw17625step1 i j = -(raw17625step0 i j); unfold raw17625step1 raw17625step0; decide +kernel
      have hl : raw17625step1Labels = raw17625step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3690 node3690Labels := by rfl

def raw17626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw17626Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17626step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17626step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17626 raw17626Labels = mixedMoment B node3683 node3683Labels := by
  calc
    mixedMoment B raw17626 raw17626Labels = mixedMoment B raw17626step0 raw17626step0Labels := by
      have ha : raw17626step0 = (fun i j => raw17626 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17626step0 raw17626; decide +kernel
      have hl : raw17626step0Labels = raw17626Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17626 raw17626Labels permutation680 permutation3
    mixedMoment B raw17626step0 raw17626step0Labels = mixedMoment B raw17626step1 raw17626step1Labels := by
      have ha : raw17626step1 = -raw17626step0 := by apply Matrix.ext; change ∀ i j, raw17626step1 i j = -(raw17626step0 i j); unfold raw17626step1 raw17626step0; decide +kernel
      have hl : raw17626step1Labels = raw17626step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3683 node3683Labels := by rfl

def raw17627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw17627Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17627step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17627 raw17627Labels = mixedMoment B node3971 node3971Labels := by
  calc
    mixedMoment B raw17627 raw17627Labels = mixedMoment B raw17627step0 raw17627step0Labels := by
      have ha : raw17627step0 = (fun i j => raw17627 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17627step0 raw17627; decide +kernel
      have hl : raw17627step0Labels = raw17627Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17627 raw17627Labels permutation159 permutation3
    _ = mixedMoment B node3971 node3971Labels := by rfl

def raw17628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17628Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw17628step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw17628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17628 raw17628Labels = mixedMoment B node1987 node1987Labels := by
  calc
    mixedMoment B raw17628 raw17628Labels = mixedMoment B raw17628step0 raw17628step0Labels := by
      have ha : raw17628step0 = (fun i j => raw17628 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17628step0 raw17628; decide +kernel
      have hl : raw17628step0Labels = raw17628Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17628 raw17628Labels permutation682 permutation3
    mixedMoment B raw17628step0 raw17628step0Labels = mixedMoment B raw17628step1 raw17628step1Labels := by
      have ha : raw17628step1 = -raw17628step0 := by apply Matrix.ext; change ∀ i j, raw17628step1 i j = -(raw17628step0 i j); unfold raw17628step1 raw17628step0; decide +kernel
      have hl : raw17628step1Labels = raw17628step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1987 node1987Labels := by rfl

def raw17629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17629step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17629step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17629 raw17629Labels = mixedMoment B node1990 node1990Labels := by
  calc
    mixedMoment B raw17629 raw17629Labels = mixedMoment B raw17629step0 raw17629step0Labels := by
      have ha : raw17629step0 = (fun i j => raw17629 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17629step0 raw17629; decide +kernel
      have hl : raw17629step0Labels = raw17629Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17629 raw17629Labels permutation681 permutation3
    mixedMoment B raw17629step0 raw17629step0Labels = mixedMoment B raw17629step1 raw17629step1Labels := by
      have ha : raw17629step1 = -raw17629step0 := by apply Matrix.ext; change ∀ i j, raw17629step1 i j = -(raw17629step0 i j); unfold raw17629step1 raw17629step0; decide +kernel
      have hl : raw17629step1Labels = raw17629step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1990 node1990Labels := by rfl

def raw17630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17630step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17630step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17630 raw17630Labels = mixedMoment B node2020 node2020Labels := by
  calc
    mixedMoment B raw17630 raw17630Labels = mixedMoment B raw17630step0 raw17630step0Labels := by
      have ha : raw17630step0 = (fun i j => raw17630 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17630step0 raw17630; decide +kernel
      have hl : raw17630step0Labels = raw17630Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17630 raw17630Labels permutation688 permutation3
    mixedMoment B raw17630step0 raw17630step0Labels = mixedMoment B raw17630step1 raw17630step1Labels := by
      have ha : raw17630step1 = -raw17630step0 := by apply Matrix.ext; change ∀ i j, raw17630step1 i j = -(raw17630step0 i j); unfold raw17630step1 raw17630step0; decide +kernel
      have hl : raw17630step1Labels = raw17630step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2020 node2020Labels := by rfl

def raw17631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw17631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17631step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17631 raw17631Labels = mixedMoment B node2000 node2000Labels := by
  calc
    mixedMoment B raw17631 raw17631Labels = mixedMoment B raw17631step0 raw17631step0Labels := by
      have ha : raw17631step0 = (fun i j => raw17631 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17631step0 raw17631; decide +kernel
      have hl : raw17631step0Labels = raw17631Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17631 raw17631Labels permutation680 permutation3
    mixedMoment B raw17631step0 raw17631step0Labels = mixedMoment B raw17631step1 raw17631step1Labels := by
      have ha : raw17631step1 = -raw17631step0 := by apply Matrix.ext; change ∀ i j, raw17631step1 i j = -(raw17631step0 i j); unfold raw17631step1 raw17631step0; decide +kernel
      have hl : raw17631step1Labels = raw17631step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2000 node2000Labels := by rfl

def raw17632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw17632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17632step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17632step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17632step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17632 raw17632Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw17632 raw17632Labels = mixedMoment B raw17632step0 raw17632step0Labels := by
      have ha : raw17632step0 = (fun i j => raw17632 (permutation640 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17632step0 raw17632; decide +kernel
      have hl : raw17632step0Labels = raw17632Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17632 raw17632Labels permutation640 permutation3
    mixedMoment B raw17632step0 raw17632step0Labels = mixedMoment B raw17632step1 raw17632step1Labels := by
      have ha : raw17632step1 = -raw17632step0 := by apply Matrix.ext; change ∀ i j, raw17632step1 i j = -(raw17632step0 i j); unfold raw17632step1 raw17632step0; decide +kernel
      have hl : raw17632step1Labels = raw17632step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2191 node2191Labels := by rfl

def raw17633 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17633Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17633step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17633step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17633step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17633step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17633step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17633 raw17633Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw17633 raw17633Labels = mixedMoment B raw17633step0 raw17633step0Labels := by
      have ha : raw17633step0 = (fun i j => raw17633 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17633step0 raw17633; decide +kernel
      have hl : raw17633step0Labels = raw17633Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17633 raw17633Labels permutation682 permutation6
    mixedMoment B raw17633step0 raw17633step0Labels = mixedMoment B raw17633step1 raw17633step1Labels := by
      have ha : raw17633step1 = -raw17633step0 := by apply Matrix.ext; change ∀ i j, raw17633step1 i j = -(raw17633step0 i j); unfold raw17633step1 raw17633step0; decide +kernel
      have hl : raw17633step1Labels = raw17633step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17633step1 raw17633step1Labels = mixedMoment B raw17633step2 raw17633step2Labels := by
      have ha : raw17633step2 = raw17633step1 := by apply Matrix.ext; unfold raw17633step2 raw17633step1; decide +kernel
      have hl : raw17633step1Labels = labelEmbedding9 ∘ raw17633step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17633step1 raw17633step1Labels raw17633step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw17634 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17634step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17634step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17634step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17634step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17634step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17634 raw17634Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw17634 raw17634Labels = mixedMoment B raw17634step0 raw17634step0Labels := by
      have hz : ∀ j, raw17634 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17634step0 = (fun i j => raw17634 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17634step0 raw17634; decide +kernel
      have hl : raw17634step0Labels = raw17634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17634 raw17634Labels permutation346 hz
    mixedMoment B raw17634step0 raw17634step0Labels = mixedMoment B raw17634step1 raw17634step1Labels := by
      have ha : raw17634step1 = (fun i j => raw17634step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17634step1 raw17634step0; decide +kernel
      have hl : raw17634step1Labels = raw17634step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17634step0 raw17634step0Labels permutation151 permutation6
    mixedMoment B raw17634step1 raw17634step1Labels = mixedMoment B raw17634step2 raw17634step2Labels := by
      have ha : raw17634step2 = -raw17634step1 := by apply Matrix.ext; change ∀ i j, raw17634step2 i j = -(raw17634step1 i j); unfold raw17634step2 raw17634step1; decide +kernel
      have hl : raw17634step2Labels = raw17634step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17634step2 raw17634step2Labels = mixedMoment B raw17634step3 raw17634step3Labels := by
      have ha : raw17634step3 = raw17634step2 := by apply Matrix.ext; unfold raw17634step3 raw17634step2; decide +kernel
      have hl : raw17634step2Labels = labelEmbedding9 ∘ raw17634step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17634step2 raw17634step2Labels raw17634step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw17635 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw17635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17635step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17635step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17635 raw17635Labels = mixedMoment B node5426 node5426Labels := by
  calc
    mixedMoment B raw17635 raw17635Labels = mixedMoment B raw17635step0 raw17635step0Labels := by
      have ha : raw17635step0 = (fun i j => raw17635 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17635step0 raw17635; decide +kernel
      have hl : raw17635step0Labels = raw17635Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17635 raw17635Labels permutation181 permutation2
    mixedMoment B raw17635step0 raw17635step0Labels = mixedMoment B raw17635step1 raw17635step1Labels := by
      have ha : raw17635step1 = -raw17635step0 := by apply Matrix.ext; change ∀ i j, raw17635step1 i j = -(raw17635step0 i j); unfold raw17635step1 raw17635step0; decide +kernel
      have hl : raw17635step1Labels = raw17635step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5426 node5426Labels := by rfl

def raw17636 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17636step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17636step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17636step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17636step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17636 raw17636Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw17636 raw17636Labels = mixedMoment B raw17636step0 raw17636step0Labels := by
      have ha : raw17636step0 = (fun i j => raw17636 (permutation644 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17636step0 raw17636; decide +kernel
      have hl : raw17636step0Labels = raw17636Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17636 raw17636Labels permutation644 permutation4
    mixedMoment B raw17636step0 raw17636step0Labels = mixedMoment B raw17636step1 raw17636step1Labels := by
      have ha : raw17636step1 = raw17636step0 := by apply Matrix.ext; unfold raw17636step1 raw17636step0; decide +kernel
      have hl : raw17636step0Labels = labelEmbedding7 ∘ raw17636step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17636step0 raw17636step0Labels raw17636step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5423 node5423Labels := by rfl

def raw17637 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17637Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17637step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17637step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17637step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17637step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17637step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17637 raw17637Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw17637 raw17637Labels = mixedMoment B raw17637step0 raw17637step0Labels := by
      have hz : ∀ j, raw17637 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17637step0 = (fun i j => raw17637 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17637step0 raw17637; decide +kernel
      have hl : raw17637step0Labels = raw17637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17637 raw17637Labels permutation346 hz
    mixedMoment B raw17637step0 raw17637step0Labels = mixedMoment B raw17637step1 raw17637step1Labels := by
      have ha : raw17637step1 = (fun i j => raw17637step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17637step1 raw17637step0; decide +kernel
      have hl : raw17637step1Labels = raw17637step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17637step0 raw17637step0Labels permutation151 permutation6
    mixedMoment B raw17637step1 raw17637step1Labels = mixedMoment B raw17637step2 raw17637step2Labels := by
      have ha : raw17637step2 = -raw17637step1 := by apply Matrix.ext; change ∀ i j, raw17637step2 i j = -(raw17637step1 i j); unfold raw17637step2 raw17637step1; decide +kernel
      have hl : raw17637step2Labels = raw17637step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17637step2 raw17637step2Labels = mixedMoment B raw17637step3 raw17637step3Labels := by
      have ha : raw17637step3 = raw17637step2 := by apply Matrix.ext; unfold raw17637step3 raw17637step2; decide +kernel
      have hl : raw17637step2Labels = labelEmbedding9 ∘ raw17637step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17637step2 raw17637step2Labels raw17637step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw17638 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17638step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17638step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17638step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17638 raw17638Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw17638 raw17638Labels = mixedMoment B raw17638step0 raw17638step0Labels := by
      have ha : raw17638step0 = (fun i j => raw17638 (permutation643 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17638step0 raw17638; decide +kernel
      have hl : raw17638step0Labels = raw17638Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17638 raw17638Labels permutation643 permutation4
    mixedMoment B raw17638step0 raw17638step0Labels = mixedMoment B raw17638step1 raw17638step1Labels := by
      have ha : raw17638step1 = raw17638step0 := by apply Matrix.ext; unfold raw17638step1 raw17638step0; decide +kernel
      have hl : raw17638step0Labels = labelEmbedding7 ∘ raw17638step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17638step0 raw17638step0Labels raw17638step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw17639 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17639Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17639step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17639step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17639step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17639 raw17639Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw17639 raw17639Labels = mixedMoment B raw17639step0 raw17639step0Labels := by
      have ha : raw17639step0 = (fun i j => raw17639 (permutation646 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17639step0 raw17639; decide +kernel
      have hl : raw17639step0Labels = raw17639Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17639 raw17639Labels permutation646 permutation4
    mixedMoment B raw17639step0 raw17639step0Labels = mixedMoment B raw17639step1 raw17639step1Labels := by
      have ha : raw17639step1 = raw17639step0 := by apply Matrix.ext; unfold raw17639step1 raw17639step0; decide +kernel
      have hl : raw17639step0Labels = labelEmbedding7 ∘ raw17639step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17639step0 raw17639step0Labels raw17639step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw17640 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17640Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17640step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17640step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17640step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17640step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17640 raw17640Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw17640 raw17640Labels = mixedMoment B raw17640step0 raw17640step0Labels := by
      have ha : raw17640step0 = (fun i j => raw17640 (permutation645 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17640step0 raw17640; decide +kernel
      have hl : raw17640step0Labels = raw17640Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17640 raw17640Labels permutation645 permutation4
    mixedMoment B raw17640step0 raw17640step0Labels = mixedMoment B raw17640step1 raw17640step1Labels := by
      have ha : raw17640step1 = raw17640step0 := by apply Matrix.ext; unfold raw17640step1 raw17640step0; decide +kernel
      have hl : raw17640step0Labels = labelEmbedding7 ∘ raw17640step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17640step0 raw17640step0Labels raw17640step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw17641 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17641step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17641step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17641 raw17641Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw17641 raw17641Labels = mixedMoment B raw17641step0 raw17641step0Labels := by
      have ha : raw17641step0 = (fun i j => raw17641 (permutation643 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17641step0 raw17641; decide +kernel
      have hl : raw17641step0Labels = raw17641Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17641 raw17641Labels permutation643 permutation4
    mixedMoment B raw17641step0 raw17641step0Labels = mixedMoment B raw17641step1 raw17641step1Labels := by
      have ha : raw17641step1 = raw17641step0 := by apply Matrix.ext; unfold raw17641step1 raw17641step0; decide +kernel
      have hl : raw17641step0Labels = labelEmbedding7 ∘ raw17641step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17641step0 raw17641step0Labels raw17641step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5381 node5381Labels := by rfl

def raw17642 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17642step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17642step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17642step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17642step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17642 raw17642Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw17642 raw17642Labels = mixedMoment B raw17642step0 raw17642step0Labels := by
      have hz : ∀ j, raw17642 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17642step0 = (fun i j => raw17642 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17642step0 raw17642; decide +kernel
      have hl : raw17642step0Labels = raw17642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17642 raw17642Labels permutation434 hz
    mixedMoment B raw17642step0 raw17642step0Labels = mixedMoment B raw17642step1 raw17642step1Labels := by
      have ha : raw17642step1 = (fun i j => raw17642step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17642step1 raw17642step0; decide +kernel
      have hl : raw17642step1Labels = raw17642step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17642step0 raw17642step0Labels permutation145 permutation4
    mixedMoment B raw17642step1 raw17642step1Labels = mixedMoment B raw17642step2 raw17642step2Labels := by
      have ha : raw17642step2 = raw17642step1 := by apply Matrix.ext; unfold raw17642step2 raw17642step1; decide +kernel
      have hl : raw17642step1Labels = labelEmbedding7 ∘ raw17642step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17642step1 raw17642step1Labels raw17642step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw17643 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17643Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17643step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17643step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17643step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17643 raw17643Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw17643 raw17643Labels = mixedMoment B raw17643step0 raw17643step0Labels := by
      have ha : raw17643step0 = (fun i j => raw17643 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17643step0 raw17643; decide +kernel
      have hl : raw17643step0Labels = raw17643Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17643 raw17643Labels permutation158 permutation6
    mixedMoment B raw17643step0 raw17643step0Labels = mixedMoment B raw17643step1 raw17643step1Labels := by
      have ha : raw17643step1 = raw17643step0 := by apply Matrix.ext; unfold raw17643step1 raw17643step0; decide +kernel
      have hl : raw17643step0Labels = labelEmbedding9 ∘ raw17643step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17643step0 raw17643step0Labels raw17643step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

def raw17644 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17644step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17644step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17644 raw17644Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw17644 raw17644Labels = mixedMoment B raw17644step0 raw17644step0Labels := by
      have ha : raw17644step0 = (fun i j => raw17644 (permutation646 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17644step0 raw17644; decide +kernel
      have hl : raw17644step0Labels = raw17644Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17644 raw17644Labels permutation646 permutation4
    mixedMoment B raw17644step0 raw17644step0Labels = mixedMoment B raw17644step1 raw17644step1Labels := by
      have ha : raw17644step1 = raw17644step0 := by apply Matrix.ext; unfold raw17644step1 raw17644step0; decide +kernel
      have hl : raw17644step0Labels = labelEmbedding7 ∘ raw17644step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17644step0 raw17644step0Labels raw17644step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw17645 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17645step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17645step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17645 raw17645Labels = mixedMoment B node5135 node5135Labels := by
  calc
    mixedMoment B raw17645 raw17645Labels = mixedMoment B raw17645step0 raw17645step0Labels := by
      have ha : raw17645step0 = (fun i j => raw17645 (permutation645 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17645step0 raw17645; decide +kernel
      have hl : raw17645step0Labels = raw17645Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17645 raw17645Labels permutation645 permutation4
    mixedMoment B raw17645step0 raw17645step0Labels = mixedMoment B raw17645step1 raw17645step1Labels := by
      have ha : raw17645step1 = raw17645step0 := by apply Matrix.ext; unfold raw17645step1 raw17645step0; decide +kernel
      have hl : raw17645step0Labels = labelEmbedding7 ∘ raw17645step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17645step0 raw17645step0Labels raw17645step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5135 node5135Labels := by rfl

def raw17646 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17646step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17646step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17646step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17646step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17646 raw17646Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw17646 raw17646Labels = mixedMoment B raw17646step0 raw17646step0Labels := by
      have hz : ∀ j, raw17646 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17646step0 = (fun i j => raw17646 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17646step0 raw17646; decide +kernel
      have hl : raw17646step0Labels = raw17646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17646 raw17646Labels permutation346 hz
    mixedMoment B raw17646step0 raw17646step0Labels = mixedMoment B raw17646step1 raw17646step1Labels := by
      have ha : raw17646step1 = (fun i j => raw17646step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17646step1 raw17646step0; decide +kernel
      have hl : raw17646step1Labels = raw17646step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17646step0 raw17646step0Labels permutation151 permutation4
    mixedMoment B raw17646step1 raw17646step1Labels = mixedMoment B raw17646step2 raw17646step2Labels := by
      have ha : raw17646step2 = raw17646step1 := by apply Matrix.ext; unfold raw17646step2 raw17646step1; decide +kernel
      have hl : raw17646step1Labels = labelEmbedding7 ∘ raw17646step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17646step1 raw17646step1Labels raw17646step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw17647 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17647step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17647step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17647step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17647step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17647 raw17647Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw17647 raw17647Labels = mixedMoment B raw17647step0 raw17647step0Labels := by
      have ha : raw17647step0 = (fun i j => raw17647 (permutation643 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17647step0 raw17647; decide +kernel
      have hl : raw17647step0Labels = raw17647Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17647 raw17647Labels permutation643 permutation4
    mixedMoment B raw17647step0 raw17647step0Labels = mixedMoment B raw17647step1 raw17647step1Labels := by
      have ha : raw17647step1 = raw17647step0 := by apply Matrix.ext; unfold raw17647step1 raw17647step0; decide +kernel
      have hl : raw17647step0Labels = labelEmbedding7 ∘ raw17647step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17647step0 raw17647step0Labels raw17647step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5138 node5138Labels := by rfl

def raw17648 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17648Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17648step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17648step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17648 raw17648Labels = mixedMoment B node3839 node3839Labels := by
  calc
    mixedMoment B raw17648 raw17648Labels = mixedMoment B raw17648step0 raw17648step0Labels := by
      have ha : raw17648step0 = (fun i j => raw17648 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17648step0 raw17648; decide +kernel
      have hl : raw17648step0Labels = raw17648Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17648 raw17648Labels permutation682 permutation6
    mixedMoment B raw17648step0 raw17648step0Labels = mixedMoment B raw17648step1 raw17648step1Labels := by
      have ha : raw17648step1 = -raw17648step0 := by apply Matrix.ext; change ∀ i j, raw17648step1 i j = -(raw17648step0 i j); unfold raw17648step1 raw17648step0; decide +kernel
      have hl : raw17648step1Labels = raw17648step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3839 node3839Labels := by rfl

def raw17649 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17649Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17649step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17649step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17649step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17649step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17649step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17649 raw17649Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw17649 raw17649Labels = mixedMoment B raw17649step0 raw17649step0Labels := by
      have hz : ∀ j, raw17649 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17649step0 = (fun i j => raw17649 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17649step0 raw17649; decide +kernel
      have hl : raw17649step0Labels = raw17649Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17649 raw17649Labels permutation346 hz
    mixedMoment B raw17649step0 raw17649step0Labels = mixedMoment B raw17649step1 raw17649step1Labels := by
      have ha : raw17649step1 = (fun i j => raw17649step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17649step1 raw17649step0; decide +kernel
      have hl : raw17649step1Labels = raw17649step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17649step0 raw17649step0Labels permutation151 permutation6
    mixedMoment B raw17649step1 raw17649step1Labels = mixedMoment B raw17649step2 raw17649step2Labels := by
      have ha : raw17649step2 = -raw17649step1 := by apply Matrix.ext; change ∀ i j, raw17649step2 i j = -(raw17649step1 i j); unfold raw17649step2 raw17649step1; decide +kernel
      have hl : raw17649step2Labels = raw17649step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw17650 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17650Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17650step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17650 raw17650Labels = mixedMoment B node3841 node3841Labels := by
  calc
    mixedMoment B raw17650 raw17650Labels = mixedMoment B raw17650step0 raw17650step0Labels := by
      have ha : raw17650step0 = (fun i j => raw17650 (permutation494 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17650step0 raw17650; decide +kernel
      have hl : raw17650step0Labels = raw17650Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17650 raw17650Labels permutation494 permutation3
    _ = mixedMoment B node3841 node3841Labels := by rfl

def raw17651 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17651Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17651step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17651 raw17651Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw17651 raw17651Labels = mixedMoment B raw17651step0 raw17651step0Labels := by
      have ha : raw17651step0 = (fun i j => raw17651 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17651step0 raw17651; decide +kernel
      have hl : raw17651step0Labels = raw17651Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17651 raw17651Labels permutation158 permutation6
    _ = mixedMoment B node3837 node3837Labels := by rfl

def raw17652 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17652Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17652step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17652step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17652step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17652step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17652step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17652step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17652 raw17652Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw17652 raw17652Labels = mixedMoment B raw17652step0 raw17652step0Labels := by
      have hz : ∀ j, raw17652 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17652step0 = (fun i j => raw17652 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17652step0 raw17652; decide +kernel
      have hl : raw17652step0Labels = raw17652Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17652 raw17652Labels permutation346 hz
    mixedMoment B raw17652step0 raw17652step0Labels = mixedMoment B raw17652step1 raw17652step1Labels := by
      have ha : raw17652step1 = (fun i j => raw17652step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17652step1 raw17652step0; decide +kernel
      have hl : raw17652step1Labels = raw17652step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17652step0 raw17652step0Labels permutation151 permutation6
    mixedMoment B raw17652step1 raw17652step1Labels = mixedMoment B raw17652step2 raw17652step2Labels := by
      have ha : raw17652step2 = -raw17652step1 := by apply Matrix.ext; change ∀ i j, raw17652step2 i j = -(raw17652step1 i j); unfold raw17652step2 raw17652step1; decide +kernel
      have hl : raw17652step2Labels = raw17652step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw17653 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17653Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17653step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17653step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17653step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17653step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17653 raw17653Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw17653 raw17653Labels = mixedMoment B raw17653step0 raw17653step0Labels := by
      have ha : raw17653step0 = (fun i j => raw17653 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17653step0 raw17653; decide +kernel
      have hl : raw17653step0Labels = raw17653Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17653 raw17653Labels permutation682 permutation6
    mixedMoment B raw17653step0 raw17653step0Labels = mixedMoment B raw17653step1 raw17653step1Labels := by
      have ha : raw17653step1 = -raw17653step0 := by apply Matrix.ext; change ∀ i j, raw17653step1 i j = -(raw17653step0 i j); unfold raw17653step1 raw17653step0; decide +kernel
      have hl : raw17653step1Labels = raw17653step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw17654 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17654Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17654step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw17654step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17654 raw17654Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw17654 raw17654Labels = mixedMoment B raw17654step0 raw17654step0Labels := by
      have ha : raw17654step0 = (fun i j => raw17654 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17654step0 raw17654; decide +kernel
      have hl : raw17654step0Labels = raw17654Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17654 raw17654Labels permutation158 permutation6
    _ = mixedMoment B node3795 node3795Labels := by rfl

def raw17655 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17655Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17655step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17655step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17655 raw17655Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw17655 raw17655Labels = mixedMoment B raw17655step0 raw17655step0Labels := by
      have ha : raw17655step0 = (fun i j => raw17655 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17655step0 raw17655; decide +kernel
      have hl : raw17655step0Labels = raw17655Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17655 raw17655Labels permutation682 permutation6
    mixedMoment B raw17655step0 raw17655step0Labels = mixedMoment B raw17655step1 raw17655step1Labels := by
      have ha : raw17655step1 = -raw17655step0 := by apply Matrix.ext; change ∀ i j, raw17655step1 i j = -(raw17655step0 i j); unfold raw17655step1 raw17655step0; decide +kernel
      have hl : raw17655step1Labels = raw17655step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw17656 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17656Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17656step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17656step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17656step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17656step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17656 raw17656Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw17656 raw17656Labels = mixedMoment B raw17656step0 raw17656step0Labels := by
      have ha : raw17656step0 = (fun i j => raw17656 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17656step0 raw17656; decide +kernel
      have hl : raw17656step0Labels = raw17656Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17656 raw17656Labels permutation682 permutation6
    mixedMoment B raw17656step0 raw17656step0Labels = mixedMoment B raw17656step1 raw17656step1Labels := by
      have ha : raw17656step1 = -raw17656step0 := by apply Matrix.ext; change ∀ i j, raw17656step1 i j = -(raw17656step0 i j); unfold raw17656step1 raw17656step0; decide +kernel
      have hl : raw17656step1Labels = raw17656step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3834 node3834Labels := by rfl

def raw17657 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17657Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17657step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17657step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17657step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17657step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17657 raw17657Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw17657 raw17657Labels = mixedMoment B raw17657step0 raw17657step0Labels := by
      have hz : ∀ j, raw17657 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17657step0 = (fun i j => raw17657 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17657step0 raw17657; decide +kernel
      have hl : raw17657step0Labels = raw17657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17657 raw17657Labels permutation434 hz
    mixedMoment B raw17657step0 raw17657step0Labels = mixedMoment B raw17657step1 raw17657step1Labels := by
      have ha : raw17657step1 = (fun i j => raw17657step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17657step1 raw17657step0; decide +kernel
      have hl : raw17657step1Labels = raw17657step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17657step0 raw17657step0Labels permutation151 permutation6
    mixedMoment B raw17657step1 raw17657step1Labels = mixedMoment B raw17657step2 raw17657step2Labels := by
      have ha : raw17657step2 = -raw17657step1 := by apply Matrix.ext; change ∀ i j, raw17657step2 i j = -(raw17657step1 i j); unfold raw17657step2 raw17657step1; decide +kernel
      have hl : raw17657step2Labels = raw17657step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw17658 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17658Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17658step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17658 raw17658Labels = mixedMoment B node3971 node3971Labels := by
  calc
    mixedMoment B raw17658 raw17658Labels = mixedMoment B raw17658step0 raw17658step0Labels := by
      have ha : raw17658step0 = (fun i j => raw17658 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17658step0 raw17658; decide +kernel
      have hl : raw17658step0Labels = raw17658Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17658 raw17658Labels permutation158 permutation6
    _ = mixedMoment B node3971 node3971Labels := by rfl

def raw17659 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17659Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw17659step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17659step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw17659step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17659 raw17659Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw17659 raw17659Labels = mixedMoment B raw17659step0 raw17659step0Labels := by
      have ha : raw17659step0 = (fun i j => raw17659 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17659step0 raw17659; decide +kernel
      have hl : raw17659step0Labels = raw17659Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17659 raw17659Labels permutation682 permutation6
    mixedMoment B raw17659step0 raw17659step0Labels = mixedMoment B raw17659step1 raw17659step1Labels := by
      have ha : raw17659step1 = -raw17659step0 := by apply Matrix.ext; change ∀ i j, raw17659step1 i j = -(raw17659step0 i j); unfold raw17659step1 raw17659step0; decide +kernel
      have hl : raw17659step1Labels = raw17659step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3514 node3514Labels := by rfl

def raw17660 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17660step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17660step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17660step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17660step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17660 raw17660Labels = mixedMoment B node3515 node3515Labels := by
  calc
    mixedMoment B raw17660 raw17660Labels = mixedMoment B raw17660step0 raw17660step0Labels := by
      have ha : raw17660step0 = (fun i j => raw17660 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17660step0 raw17660; decide +kernel
      have hl : raw17660step0Labels = raw17660Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17660 raw17660Labels permutation682 permutation6
    mixedMoment B raw17660step0 raw17660step0Labels = mixedMoment B raw17660step1 raw17660step1Labels := by
      have ha : raw17660step1 = -raw17660step0 := by apply Matrix.ext; change ∀ i j, raw17660step1 i j = -(raw17660step0 i j); unfold raw17660step1 raw17660step0; decide +kernel
      have hl : raw17660step1Labels = raw17660step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3515 node3515Labels := by rfl

def raw17661 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17661step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17661step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17661step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17661step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17661 raw17661Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw17661 raw17661Labels = mixedMoment B raw17661step0 raw17661step0Labels := by
      have hz : ∀ j, raw17661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17661step0 = (fun i j => raw17661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17661step0 raw17661; decide +kernel
      have hl : raw17661step0Labels = raw17661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17661 raw17661Labels permutation346 hz
    mixedMoment B raw17661step0 raw17661step0Labels = mixedMoment B raw17661step1 raw17661step1Labels := by
      have ha : raw17661step1 = (fun i j => raw17661step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17661step1 raw17661step0; decide +kernel
      have hl : raw17661step1Labels = raw17661step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17661step0 raw17661step0Labels permutation151 permutation6
    mixedMoment B raw17661step1 raw17661step1Labels = mixedMoment B raw17661step2 raw17661step2Labels := by
      have ha : raw17661step2 = -raw17661step1 := by apply Matrix.ext; change ∀ i j, raw17661step2 i j = -(raw17661step1 i j); unfold raw17661step2 raw17661step1; decide +kernel
      have hl : raw17661step2Labels = raw17661step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw17662 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2]]
def raw17662Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17662step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17662step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17662 raw17662Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw17662 raw17662Labels = mixedMoment B raw17662step0 raw17662step0Labels := by
      have ha : raw17662step0 = (fun i j => raw17662 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17662step0 raw17662; decide +kernel
      have hl : raw17662step0Labels = raw17662Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17662 raw17662Labels permutation682 permutation6
    mixedMoment B raw17662step0 raw17662step0Labels = mixedMoment B raw17662step1 raw17662step1Labels := by
      have ha : raw17662step1 = -raw17662step0 := by apply Matrix.ext; change ∀ i j, raw17662step1 i j = -(raw17662step0 i j); unfold raw17662step1 raw17662step0; decide +kernel
      have hl : raw17662step1Labels = raw17662step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3517 node3517Labels := by rfl

def raw17663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17663Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17663step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17663step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17663step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17663step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17663step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17663 raw17663Labels = mixedMoment B node5487 node5487Labels := by
  calc
    mixedMoment B raw17663 raw17663Labels = mixedMoment B raw17663step0 raw17663step0Labels := by
      have hz : ∀ j, raw17663 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17663step0 = (fun i j => raw17663 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17663step0 raw17663; decide +kernel
      have hl : raw17663step0Labels = raw17663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17663 raw17663Labels permutation434 hz
    mixedMoment B raw17663step0 raw17663step0Labels = mixedMoment B raw17663step1 raw17663step1Labels := by
      have hz : ∀ j, raw17663step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17663step1 = (fun i j => raw17663step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17663step1 raw17663step0; decide +kernel
      have hl : raw17663step1Labels = raw17663step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17663step0 raw17663step0Labels permutation80 hz
    mixedMoment B raw17663step1 raw17663step1Labels = mixedMoment B raw17663step2 raw17663step2Labels := by
      have ha : raw17663step2 = (fun i j => raw17663step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17663step2 raw17663step1; decide +kernel
      have hl : raw17663step2Labels = raw17663step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17663step1 raw17663step1Labels permutation14 permutation2
    _ = mixedMoment B node5487 node5487Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
