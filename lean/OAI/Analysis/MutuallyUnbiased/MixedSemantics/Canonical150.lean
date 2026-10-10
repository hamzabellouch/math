import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw19200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw19200step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19200step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19200step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw19200step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19200 raw19200Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw19200 raw19200Labels = mixedMoment B raw19200step0 raw19200step0Labels := by
      have hz : ∀ j, raw19200 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19200step0 = (fun i j => raw19200 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19200step0 raw19200; decide +kernel
      have hl : raw19200step0Labels = raw19200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19200 raw19200Labels permutation590 hz
    mixedMoment B raw19200step0 raw19200step0Labels = mixedMoment B raw19200step1 raw19200step1Labels := by
      have ha : raw19200step1 = (fun i j => raw19200step0 (permutation41 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19200step1 raw19200step0; decide +kernel
      have hl : raw19200step1Labels = raw19200step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19200step0 raw19200step0Labels permutation41 permutation6
    mixedMoment B raw19200step1 raw19200step1Labels = mixedMoment B raw19200step2 raw19200step2Labels := by
      have ha : raw19200step2 = -raw19200step1 := by apply Matrix.ext; change ∀ i j, raw19200step2 i j = -(raw19200step1 i j); unfold raw19200step2 raw19200step1; decide +kernel
      have hl : raw19200step2Labels = raw19200step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19200step2 raw19200step2Labels = mixedMoment B raw19200step3 raw19200step3Labels := by
      have ha : raw19200step3 = raw19200step2 := by apply Matrix.ext; unfold raw19200step3 raw19200step2; decide +kernel
      have hl : raw19200step2Labels = labelEmbedding9 ∘ raw19200step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19200step2 raw19200step2Labels raw19200step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw19201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19201step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19201 raw19201Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw19201 raw19201Labels = mixedMoment B raw19201step0 raw19201step0Labels := by
      have ha : raw19201step0 = (fun i j => raw19201 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19201step0 raw19201; decide +kernel
      have hl : raw19201step0Labels = raw19201Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19201 raw19201Labels permutation180 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw19202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19202step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19202step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19202step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19202step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19202step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19202 raw19202Labels = mixedMoment B node5220 node5220Labels := by
  calc
    mixedMoment B raw19202 raw19202Labels = mixedMoment B raw19202step0 raw19202step0Labels := by
      have ha : raw19202step0 = (fun i j => raw19202 (permutation274 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19202step0 raw19202; decide +kernel
      have hl : raw19202step0Labels = raw19202Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19202 raw19202Labels permutation274 permutation5
    mixedMoment B raw19202step0 raw19202step0Labels = mixedMoment B raw19202step1 raw19202step1Labels := by
      have ha : raw19202step1 = -raw19202step0 := by apply Matrix.ext; change ∀ i j, raw19202step1 i j = -(raw19202step0 i j); unfold raw19202step1 raw19202step0; decide +kernel
      have hl : raw19202step1Labels = raw19202step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19202step1 raw19202step1Labels = mixedMoment B raw19202step2 raw19202step2Labels := by
      have ha : raw19202step2 = raw19202step1 := by apply Matrix.ext; unfold raw19202step2 raw19202step1; decide +kernel
      have hl : raw19202step1Labels = labelEmbedding8 ∘ raw19202step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19202step1 raw19202step1Labels raw19202step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5220 node5220Labels := by rfl

def raw19203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19203 raw19203Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw19203 raw19203Labels = mixedMoment B raw19203step0 raw19203step0Labels := by
      have ha : raw19203step0 = (fun i j => raw19203 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19203step0 raw19203; decide +kernel
      have hl : raw19203step0Labels = raw19203Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19203 raw19203Labels permutation159 permutation2
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw19204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19204step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19204 raw19204Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw19204 raw19204Labels = mixedMoment B raw19204step0 raw19204step0Labels := by
      have ha : raw19204step0 = (fun i j => raw19204 (permutation165 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19204step0 raw19204; decide +kernel
      have hl : raw19204step0Labels = raw19204Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19204 raw19204Labels permutation165 permutation2
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw19205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19205 raw19205Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw19205 raw19205Labels = mixedMoment B raw19205step0 raw19205step0Labels := by
      have hz : ∀ j, raw19205 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19205step0 = (fun i j => raw19205 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19205step0 raw19205; decide +kernel
      have hl : raw19205step0Labels = raw19205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19205 raw19205Labels permutation590 hz
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw19206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw19206step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19206step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19206step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19206step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19206step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19206 raw19206Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw19206 raw19206Labels = mixedMoment B raw19206step0 raw19206step0Labels := by
      have ha : raw19206step0 = (fun i j => raw19206 (permutation278 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19206step0 raw19206; decide +kernel
      have hl : raw19206step0Labels = raw19206Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19206 raw19206Labels permutation278 permutation5
    mixedMoment B raw19206step0 raw19206step0Labels = mixedMoment B raw19206step1 raw19206step1Labels := by
      have ha : raw19206step1 = -raw19206step0 := by apply Matrix.ext; change ∀ i j, raw19206step1 i j = -(raw19206step0 i j); unfold raw19206step1 raw19206step0; decide +kernel
      have hl : raw19206step1Labels = raw19206step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19206step1 raw19206step1Labels = mixedMoment B raw19206step2 raw19206step2Labels := by
      have ha : raw19206step2 = raw19206step1 := by apply Matrix.ext; unfold raw19206step2 raw19206step1; decide +kernel
      have hl : raw19206step1Labels = labelEmbedding8 ∘ raw19206step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19206step1 raw19206step1Labels raw19206step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw19207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19207step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19207 raw19207Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw19207 raw19207Labels = mixedMoment B raw19207step0 raw19207step0Labels := by
      have ha : raw19207step0 = (fun i j => raw19207 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19207step0 raw19207; decide +kernel
      have hl : raw19207step0Labels = raw19207Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19207 raw19207Labels permutation181 permutation2
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw19208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19208step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw19208step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19208step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw19208step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19208step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw19208step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19208 raw19208Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw19208 raw19208Labels = mixedMoment B raw19208step0 raw19208step0Labels := by
      have ha : raw19208step0 = (fun i j => raw19208 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19208step0 raw19208; decide +kernel
      have hl : raw19208step0Labels = raw19208Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19208 raw19208Labels permutation195 permutation7
    mixedMoment B raw19208step0 raw19208step0Labels = mixedMoment B raw19208step1 raw19208step1Labels := by
      have ha : raw19208step1 = -raw19208step0 := by apply Matrix.ext; change ∀ i j, raw19208step1 i j = -(raw19208step0 i j); unfold raw19208step1 raw19208step0; decide +kernel
      have hl : raw19208step1Labels = raw19208step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19208step1 raw19208step1Labels = mixedMoment B raw19208step2 raw19208step2Labels := by
      have ha : raw19208step2 = raw19208step1 := by apply Matrix.ext; unfold raw19208step2 raw19208step1; decide +kernel
      have hl : raw19208step1Labels = labelEmbedding10 ∘ raw19208step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19208step1 raw19208step1Labels raw19208step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw19209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw19209step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19209step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19209step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19209step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19209step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19209step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19209 raw19209Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw19209 raw19209Labels = mixedMoment B raw19209step0 raw19209step0Labels := by
      have hz : ∀ j, raw19209 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19209step0 = (fun i j => raw19209 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19209step0 raw19209; decide +kernel
      have hl : raw19209step0Labels = raw19209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19209 raw19209Labels permutation590 hz
    mixedMoment B raw19209step0 raw19209step0Labels = mixedMoment B raw19209step1 raw19209step1Labels := by
      have ha : raw19209step1 = (fun i j => raw19209step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19209step1 raw19209step0; decide +kernel
      have hl : raw19209step1Labels = raw19209step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19209step0 raw19209step0Labels permutation39 permutation7
    mixedMoment B raw19209step1 raw19209step1Labels = mixedMoment B raw19209step2 raw19209step2Labels := by
      have ha : raw19209step2 = -raw19209step1 := by apply Matrix.ext; change ∀ i j, raw19209step2 i j = -(raw19209step1 i j); unfold raw19209step2 raw19209step1; decide +kernel
      have hl : raw19209step2Labels = raw19209step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19209step2 raw19209step2Labels = mixedMoment B raw19209step3 raw19209step3Labels := by
      have ha : raw19209step3 = raw19209step2 := by apply Matrix.ext; unfold raw19209step3 raw19209step2; decide +kernel
      have hl : raw19209step2Labels = labelEmbedding10 ∘ raw19209step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19209step2 raw19209step2Labels raw19209step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw19210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw19210step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19210step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19210step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19210step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19210step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19210 raw19210Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw19210 raw19210Labels = mixedMoment B raw19210step0 raw19210step0Labels := by
      have ha : raw19210step0 = (fun i j => raw19210 (permutation272 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19210step0 raw19210; decide +kernel
      have hl : raw19210step0Labels = raw19210Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19210 raw19210Labels permutation272 permutation5
    mixedMoment B raw19210step0 raw19210step0Labels = mixedMoment B raw19210step1 raw19210step1Labels := by
      have ha : raw19210step1 = -raw19210step0 := by apply Matrix.ext; change ∀ i j, raw19210step1 i j = -(raw19210step0 i j); unfold raw19210step1 raw19210step0; decide +kernel
      have hl : raw19210step1Labels = raw19210step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19210step1 raw19210step1Labels = mixedMoment B raw19210step2 raw19210step2Labels := by
      have ha : raw19210step2 = raw19210step1 := by apply Matrix.ext; unfold raw19210step2 raw19210step1; decide +kernel
      have hl : raw19210step1Labels = labelEmbedding8 ∘ raw19210step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19210step1 raw19210step1Labels raw19210step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw19211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw19211step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19211 raw19211Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw19211 raw19211Labels = mixedMoment B raw19211step0 raw19211step0Labels := by
      have ha : raw19211step0 = (fun i j => raw19211 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19211step0 raw19211; decide +kernel
      have hl : raw19211step0Labels = raw19211Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19211 raw19211Labels permutation180 permutation2
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw19212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw19212step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw19212step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19212step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw19212step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19212 raw19212Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw19212 raw19212Labels = mixedMoment B raw19212step0 raw19212step0Labels := by
      have ha : raw19212step0 = (fun i j => raw19212 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19212step0 raw19212; decide +kernel
      have hl : raw19212step0Labels = raw19212Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19212 raw19212Labels permutation194 permutation7
    mixedMoment B raw19212step0 raw19212step0Labels = mixedMoment B raw19212step1 raw19212step1Labels := by
      have ha : raw19212step1 = -raw19212step0 := by apply Matrix.ext; change ∀ i j, raw19212step1 i j = -(raw19212step0 i j); unfold raw19212step1 raw19212step0; decide +kernel
      have hl : raw19212step1Labels = raw19212step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19212step1 raw19212step1Labels = mixedMoment B raw19212step2 raw19212step2Labels := by
      have ha : raw19212step2 = raw19212step1 := by apply Matrix.ext; unfold raw19212step2 raw19212step1; decide +kernel
      have hl : raw19212step1Labels = labelEmbedding10 ∘ raw19212step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19212step1 raw19212step1Labels raw19212step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw19213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw19213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19213step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19213step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19213step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19213step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19213step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19213 raw19213Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw19213 raw19213Labels = mixedMoment B raw19213step0 raw19213step0Labels := by
      have hz : ∀ j, raw19213 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19213step0 = (fun i j => raw19213 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19213step0 raw19213; decide +kernel
      have hl : raw19213step0Labels = raw19213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19213 raw19213Labels permutation590 hz
    mixedMoment B raw19213step0 raw19213step0Labels = mixedMoment B raw19213step1 raw19213step1Labels := by
      have ha : raw19213step1 = (fun i j => raw19213step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19213step1 raw19213step0; decide +kernel
      have hl : raw19213step1Labels = raw19213step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19213step0 raw19213step0Labels permutation38 permutation7
    mixedMoment B raw19213step1 raw19213step1Labels = mixedMoment B raw19213step2 raw19213step2Labels := by
      have ha : raw19213step2 = -raw19213step1 := by apply Matrix.ext; change ∀ i j, raw19213step2 i j = -(raw19213step1 i j); unfold raw19213step2 raw19213step1; decide +kernel
      have hl : raw19213step2Labels = raw19213step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19213step2 raw19213step2Labels = mixedMoment B raw19213step3 raw19213step3Labels := by
      have ha : raw19213step3 = raw19213step2 := by apply Matrix.ext; unfold raw19213step3 raw19213step2; decide +kernel
      have hl : raw19213step2Labels = labelEmbedding10 ∘ raw19213step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19213step2 raw19213step2Labels raw19213step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw19214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw19214step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19214step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw19214step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19214step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw19214step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19214 raw19214Labels = mixedMoment B node5219 node5219Labels := by
  calc
    mixedMoment B raw19214 raw19214Labels = mixedMoment B raw19214step0 raw19214step0Labels := by
      have ha : raw19214step0 = (fun i j => raw19214 (permutation273 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19214step0 raw19214; decide +kernel
      have hl : raw19214step0Labels = raw19214Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19214 raw19214Labels permutation273 permutation5
    mixedMoment B raw19214step0 raw19214step0Labels = mixedMoment B raw19214step1 raw19214step1Labels := by
      have ha : raw19214step1 = -raw19214step0 := by apply Matrix.ext; change ∀ i j, raw19214step1 i j = -(raw19214step0 i j); unfold raw19214step1 raw19214step0; decide +kernel
      have hl : raw19214step1Labels = raw19214step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19214step1 raw19214step1Labels = mixedMoment B raw19214step2 raw19214step2Labels := by
      have ha : raw19214step2 = raw19214step1 := by apply Matrix.ext; unfold raw19214step2 raw19214step1; decide +kernel
      have hl : raw19214step1Labels = labelEmbedding8 ∘ raw19214step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19214step1 raw19214step1Labels raw19214step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5219 node5219Labels := by rfl

def raw19215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19215step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19215 raw19215Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw19215 raw19215Labels = mixedMoment B raw19215step0 raw19215step0Labels := by
      have ha : raw19215step0 = (fun i j => raw19215 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19215step0 raw19215; decide +kernel
      have hl : raw19215step0Labels = raw19215Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19215 raw19215Labels permutation176 permutation2
    _ = mixedMoment B node5403 node5403Labels := by rfl

def raw19216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw19216step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19216step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw19216step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19216step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw19216step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19216 raw19216Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw19216 raw19216Labels = mixedMoment B raw19216step0 raw19216step0Labels := by
      have ha : raw19216step0 = (fun i j => raw19216 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19216step0 raw19216; decide +kernel
      have hl : raw19216step0Labels = raw19216Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19216 raw19216Labels permutation682 permutation3
    mixedMoment B raw19216step0 raw19216step0Labels = mixedMoment B raw19216step1 raw19216step1Labels := by
      have ha : raw19216step1 = -raw19216step0 := by apply Matrix.ext; change ∀ i j, raw19216step1 i j = -(raw19216step0 i j); unfold raw19216step1 raw19216step0; decide +kernel
      have hl : raw19216step1Labels = raw19216step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19216step1 raw19216step1Labels = mixedMoment B raw19216step2 raw19216step2Labels := by
      have ha : raw19216step2 = raw19216step1 := by apply Matrix.ext; unfold raw19216step2 raw19216step1; decide +kernel
      have hl : raw19216step1Labels = labelEmbedding6 ∘ raw19216step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19216step1 raw19216step1Labels raw19216step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw19217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw19217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw19217step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19217step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw19217step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19217step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw19217step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19217 raw19217Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw19217 raw19217Labels = mixedMoment B raw19217step0 raw19217step0Labels := by
      have ha : raw19217step0 = (fun i j => raw19217 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19217step0 raw19217; decide +kernel
      have hl : raw19217step0Labels = raw19217Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19217 raw19217Labels permutation658 permutation3
    mixedMoment B raw19217step0 raw19217step0Labels = mixedMoment B raw19217step1 raw19217step1Labels := by
      have ha : raw19217step1 = -raw19217step0 := by apply Matrix.ext; change ∀ i j, raw19217step1 i j = -(raw19217step0 i j); unfold raw19217step1 raw19217step0; decide +kernel
      have hl : raw19217step1Labels = raw19217step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19217step1 raw19217step1Labels = mixedMoment B raw19217step2 raw19217step2Labels := by
      have ha : raw19217step2 = raw19217step1 := by apply Matrix.ext; unfold raw19217step2 raw19217step1; decide +kernel
      have hl : raw19217step1Labels = labelEmbedding6 ∘ raw19217step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19217step1 raw19217step1Labels raw19217step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw19218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19218Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19218step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19218step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19218step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19218step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19218step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19218 raw19218Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw19218 raw19218Labels = mixedMoment B raw19218step0 raw19218step0Labels := by
      have ha : raw19218step0 = (fun i j => raw19218 (permutation313 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19218step0 raw19218; decide +kernel
      have hl : raw19218step0Labels = raw19218Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19218 raw19218Labels permutation313 permutation5
    mixedMoment B raw19218step0 raw19218step0Labels = mixedMoment B raw19218step1 raw19218step1Labels := by
      have ha : raw19218step1 = -raw19218step0 := by apply Matrix.ext; change ∀ i j, raw19218step1 i j = -(raw19218step0 i j); unfold raw19218step1 raw19218step0; decide +kernel
      have hl : raw19218step1Labels = raw19218step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19218step1 raw19218step1Labels = mixedMoment B raw19218step2 raw19218step2Labels := by
      have ha : raw19218step2 = raw19218step1 := by apply Matrix.ext; unfold raw19218step2 raw19218step1; decide +kernel
      have hl : raw19218step1Labels = labelEmbedding1 ∘ raw19218step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19218step1 raw19218step1Labels raw19218step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw19219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19219Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19219step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19219step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19219step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19219step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19219step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19219 raw19219Labels = mixedMoment B node3979 node3979Labels := by
  calc
    mixedMoment B raw19219 raw19219Labels = mixedMoment B raw19219step0 raw19219step0Labels := by
      have ha : raw19219step0 = (fun i j => raw19219 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19219step0 raw19219; decide +kernel
      have hl : raw19219step0Labels = raw19219Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19219 raw19219Labels permutation194 permutation7
    mixedMoment B raw19219step0 raw19219step0Labels = mixedMoment B raw19219step1 raw19219step1Labels := by
      have ha : raw19219step1 = -raw19219step0 := by apply Matrix.ext; change ∀ i j, raw19219step1 i j = -(raw19219step0 i j); unfold raw19219step1 raw19219step0; decide +kernel
      have hl : raw19219step1Labels = raw19219step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19219step1 raw19219step1Labels = mixedMoment B raw19219step2 raw19219step2Labels := by
      have ha : raw19219step2 = raw19219step1 := by apply Matrix.ext; unfold raw19219step2 raw19219step1; decide +kernel
      have hl : raw19219step1Labels = labelEmbedding1 ∘ raw19219step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19219step1 raw19219step1Labels raw19219step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3979 node3979Labels := by rfl

def raw19220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19220Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19220step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19220step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19220step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19220step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19220 raw19220Labels = mixedMoment B node3994 node3994Labels := by
  calc
    mixedMoment B raw19220 raw19220Labels = mixedMoment B raw19220step0 raw19220step0Labels := by
      have ha : raw19220step0 = (fun i j => raw19220 (permutation313 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19220step0 raw19220; decide +kernel
      have hl : raw19220step0Labels = raw19220Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19220 raw19220Labels permutation313 permutation5
    mixedMoment B raw19220step0 raw19220step0Labels = mixedMoment B raw19220step1 raw19220step1Labels := by
      have ha : raw19220step1 = -raw19220step0 := by apply Matrix.ext; change ∀ i j, raw19220step1 i j = -(raw19220step0 i j); unfold raw19220step1 raw19220step0; decide +kernel
      have hl : raw19220step1Labels = raw19220step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19220step1 raw19220step1Labels = mixedMoment B raw19220step2 raw19220step2Labels := by
      have ha : raw19220step2 = raw19220step1 := by apply Matrix.ext; unfold raw19220step2 raw19220step1; decide +kernel
      have hl : raw19220step1Labels = labelEmbedding1 ∘ raw19220step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19220step1 raw19220step1Labels raw19220step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3994 node3994Labels := by rfl

def raw19221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19221Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19221step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19221step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19221step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19221step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19221step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19221 raw19221Labels = mixedMoment B node3994 node3994Labels := by
  calc
    mixedMoment B raw19221 raw19221Labels = mixedMoment B raw19221step0 raw19221step0Labels := by
      have ha : raw19221step0 = (fun i j => raw19221 (permutation327 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19221step0 raw19221; decide +kernel
      have hl : raw19221step0Labels = raw19221Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19221 raw19221Labels permutation327 permutation5
    mixedMoment B raw19221step0 raw19221step0Labels = mixedMoment B raw19221step1 raw19221step1Labels := by
      have ha : raw19221step1 = -raw19221step0 := by apply Matrix.ext; change ∀ i j, raw19221step1 i j = -(raw19221step0 i j); unfold raw19221step1 raw19221step0; decide +kernel
      have hl : raw19221step1Labels = raw19221step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19221step1 raw19221step1Labels = mixedMoment B raw19221step2 raw19221step2Labels := by
      have ha : raw19221step2 = raw19221step1 := by apply Matrix.ext; unfold raw19221step2 raw19221step1; decide +kernel
      have hl : raw19221step1Labels = labelEmbedding1 ∘ raw19221step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19221step1 raw19221step1Labels raw19221step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3994 node3994Labels := by rfl

def raw19222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19222Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19222step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19222step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19222step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19222step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19222step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19222step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19222 raw19222Labels = mixedMoment B node3998 node3998Labels := by
  calc
    mixedMoment B raw19222 raw19222Labels = mixedMoment B raw19222step0 raw19222step0Labels := by
      have hz : ∀ j, raw19222 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19222step0 = (fun i j => raw19222 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19222step0 raw19222; decide +kernel
      have hl : raw19222step0Labels = raw19222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19222 raw19222Labels permutation590 hz
    mixedMoment B raw19222step0 raw19222step0Labels = mixedMoment B raw19222step1 raw19222step1Labels := by
      have ha : raw19222step1 = (fun i j => raw19222step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19222step1 raw19222step0; decide +kernel
      have hl : raw19222step1Labels = raw19222step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19222step0 raw19222step0Labels permutation38 permutation7
    mixedMoment B raw19222step1 raw19222step1Labels = mixedMoment B raw19222step2 raw19222step2Labels := by
      have ha : raw19222step2 = -raw19222step1 := by apply Matrix.ext; change ∀ i j, raw19222step2 i j = -(raw19222step1 i j); unfold raw19222step2 raw19222step1; decide +kernel
      have hl : raw19222step2Labels = raw19222step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19222step2 raw19222step2Labels = mixedMoment B raw19222step3 raw19222step3Labels := by
      have ha : raw19222step3 = raw19222step2 := by apply Matrix.ext; unfold raw19222step3 raw19222step2; decide +kernel
      have hl : raw19222step2Labels = labelEmbedding1 ∘ raw19222step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19222step2 raw19222step2Labels raw19222step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3998 node3998Labels := by rfl

def raw19223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19223Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19223step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw19223step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19223step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19223step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19223step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19223step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19223 raw19223Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw19223 raw19223Labels = mixedMoment B raw19223step0 raw19223step0Labels := by
      have ha : raw19223step0 = (fun i j => raw19223 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19223step0 raw19223; decide +kernel
      have hl : raw19223step0Labels = raw19223Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19223 raw19223Labels permutation194 permutation7
    mixedMoment B raw19223step0 raw19223step0Labels = mixedMoment B raw19223step1 raw19223step1Labels := by
      have ha : raw19223step1 = -raw19223step0 := by apply Matrix.ext; change ∀ i j, raw19223step1 i j = -(raw19223step0 i j); unfold raw19223step1 raw19223step0; decide +kernel
      have hl : raw19223step1Labels = raw19223step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19223step1 raw19223step1Labels = mixedMoment B raw19223step2 raw19223step2Labels := by
      have ha : raw19223step2 = raw19223step1 := by apply Matrix.ext; unfold raw19223step2 raw19223step1; decide +kernel
      have hl : raw19223step1Labels = labelEmbedding1 ∘ raw19223step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19223step1 raw19223step1Labels raw19223step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

def raw19224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19224Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19224step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19224step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19224step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19224step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19224step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19224 raw19224Labels = mixedMoment B node2662 node2662Labels := by
  calc
    mixedMoment B raw19224 raw19224Labels = mixedMoment B raw19224step0 raw19224step0Labels := by
      have ha : raw19224step0 = (fun i j => raw19224 (permutation274 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19224step0 raw19224; decide +kernel
      have hl : raw19224step0Labels = raw19224Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19224 raw19224Labels permutation274 permutation5
    mixedMoment B raw19224step0 raw19224step0Labels = mixedMoment B raw19224step1 raw19224step1Labels := by
      have ha : raw19224step1 = -raw19224step0 := by apply Matrix.ext; change ∀ i j, raw19224step1 i j = -(raw19224step0 i j); unfold raw19224step1 raw19224step0; decide +kernel
      have hl : raw19224step1Labels = raw19224step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19224step1 raw19224step1Labels = mixedMoment B raw19224step2 raw19224step2Labels := by
      have ha : raw19224step2 = raw19224step1 := by apply Matrix.ext; unfold raw19224step2 raw19224step1; decide +kernel
      have hl : raw19224step1Labels = labelEmbedding1 ∘ raw19224step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19224step1 raw19224step1Labels raw19224step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2662 node2662Labels := by rfl

def raw19225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19225Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19225step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19225step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19225step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19225step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19225step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19225 raw19225Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw19225 raw19225Labels = mixedMoment B raw19225step0 raw19225step0Labels := by
      have ha : raw19225step0 = (fun i j => raw19225 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19225step0 raw19225; decide +kernel
      have hl : raw19225step0Labels = raw19225Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19225 raw19225Labels permutation194 permutation7
    mixedMoment B raw19225step0 raw19225step0Labels = mixedMoment B raw19225step1 raw19225step1Labels := by
      have ha : raw19225step1 = -raw19225step0 := by apply Matrix.ext; change ∀ i j, raw19225step1 i j = -(raw19225step0 i j); unfold raw19225step1 raw19225step0; decide +kernel
      have hl : raw19225step1Labels = raw19225step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19225step1 raw19225step1Labels = mixedMoment B raw19225step2 raw19225step2Labels := by
      have ha : raw19225step2 = raw19225step1 := by apply Matrix.ext; unfold raw19225step2 raw19225step1; decide +kernel
      have hl : raw19225step1Labels = labelEmbedding1 ∘ raw19225step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19225step1 raw19225step1Labels raw19225step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw19226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19226Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19226step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19226step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19226step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19226step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw19226step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19226 raw19226Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw19226 raw19226Labels = mixedMoment B raw19226step0 raw19226step0Labels := by
      have ha : raw19226step0 = (fun i j => raw19226 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19226step0 raw19226; decide +kernel
      have hl : raw19226step0Labels = raw19226Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19226 raw19226Labels permutation195 permutation7
    mixedMoment B raw19226step0 raw19226step0Labels = mixedMoment B raw19226step1 raw19226step1Labels := by
      have ha : raw19226step1 = -raw19226step0 := by apply Matrix.ext; change ∀ i j, raw19226step1 i j = -(raw19226step0 i j); unfold raw19226step1 raw19226step0; decide +kernel
      have hl : raw19226step1Labels = raw19226step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19226step1 raw19226step1Labels = mixedMoment B raw19226step2 raw19226step2Labels := by
      have ha : raw19226step2 = raw19226step1 := by apply Matrix.ext; unfold raw19226step2 raw19226step1; decide +kernel
      have hl : raw19226step1Labels = labelEmbedding1 ∘ raw19226step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19226step1 raw19226step1Labels raw19226step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw19227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19227Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19227step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19227step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19227step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19227step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19227step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19227step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19227 raw19227Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw19227 raw19227Labels = mixedMoment B raw19227step0 raw19227step0Labels := by
      have hz : ∀ j, raw19227 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19227step0 = (fun i j => raw19227 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19227step0 raw19227; decide +kernel
      have hl : raw19227step0Labels = raw19227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19227 raw19227Labels permutation590 hz
    mixedMoment B raw19227step0 raw19227step0Labels = mixedMoment B raw19227step1 raw19227step1Labels := by
      have ha : raw19227step1 = (fun i j => raw19227step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19227step1 raw19227step0; decide +kernel
      have hl : raw19227step1Labels = raw19227step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19227step0 raw19227step0Labels permutation38 permutation7
    mixedMoment B raw19227step1 raw19227step1Labels = mixedMoment B raw19227step2 raw19227step2Labels := by
      have ha : raw19227step2 = -raw19227step1 := by apply Matrix.ext; change ∀ i j, raw19227step2 i j = -(raw19227step1 i j); unfold raw19227step2 raw19227step1; decide +kernel
      have hl : raw19227step2Labels = raw19227step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19227step2 raw19227step2Labels = mixedMoment B raw19227step3 raw19227step3Labels := by
      have ha : raw19227step3 = raw19227step2 := by apply Matrix.ext; unfold raw19227step3 raw19227step2; decide +kernel
      have hl : raw19227step2Labels = labelEmbedding1 ∘ raw19227step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19227step2 raw19227step2Labels raw19227step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3885 node3885Labels := by rfl

def raw19228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19228Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw19228step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19228step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19228step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19228step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19228step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19228 raw19228Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw19228 raw19228Labels = mixedMoment B raw19228step0 raw19228step0Labels := by
      have ha : raw19228step0 = (fun i j => raw19228 (permutation278 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19228step0 raw19228; decide +kernel
      have hl : raw19228step0Labels = raw19228Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19228 raw19228Labels permutation278 permutation5
    mixedMoment B raw19228step0 raw19228step0Labels = mixedMoment B raw19228step1 raw19228step1Labels := by
      have ha : raw19228step1 = -raw19228step0 := by apply Matrix.ext; change ∀ i j, raw19228step1 i j = -(raw19228step0 i j); unfold raw19228step1 raw19228step0; decide +kernel
      have hl : raw19228step1Labels = raw19228step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19228step1 raw19228step1Labels = mixedMoment B raw19228step2 raw19228step2Labels := by
      have ha : raw19228step2 = raw19228step1 := by apply Matrix.ext; unfold raw19228step2 raw19228step1; decide +kernel
      have hl : raw19228step1Labels = labelEmbedding1 ∘ raw19228step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19228step1 raw19228step1Labels raw19228step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw19229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19229Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19229step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19229step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19229step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19229step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19229step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19229step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19229 raw19229Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw19229 raw19229Labels = mixedMoment B raw19229step0 raw19229step0Labels := by
      have ha : raw19229step0 = (fun i j => raw19229 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19229step0 raw19229; decide +kernel
      have hl : raw19229step0Labels = raw19229Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19229 raw19229Labels permutation195 permutation7
    mixedMoment B raw19229step0 raw19229step0Labels = mixedMoment B raw19229step1 raw19229step1Labels := by
      have ha : raw19229step1 = -raw19229step0 := by apply Matrix.ext; change ∀ i j, raw19229step1 i j = -(raw19229step0 i j); unfold raw19229step1 raw19229step0; decide +kernel
      have hl : raw19229step1Labels = raw19229step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19229step1 raw19229step1Labels = mixedMoment B raw19229step2 raw19229step2Labels := by
      have ha : raw19229step2 = raw19229step1 := by apply Matrix.ext; unfold raw19229step2 raw19229step1; decide +kernel
      have hl : raw19229step1Labels = labelEmbedding1 ∘ raw19229step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19229step1 raw19229step1Labels raw19229step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

def raw19230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19230Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw19230step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19230step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw19230step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19230step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw19230step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19230 raw19230Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw19230 raw19230Labels = mixedMoment B raw19230step0 raw19230step0Labels := by
      have ha : raw19230step0 = (fun i j => raw19230 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19230step0 raw19230; decide +kernel
      have hl : raw19230step0Labels = raw19230Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19230 raw19230Labels permutation195 permutation7
    mixedMoment B raw19230step0 raw19230step0Labels = mixedMoment B raw19230step1 raw19230step1Labels := by
      have ha : raw19230step1 = -raw19230step0 := by apply Matrix.ext; change ∀ i j, raw19230step1 i j = -(raw19230step0 i j); unfold raw19230step1 raw19230step0; decide +kernel
      have hl : raw19230step1Labels = raw19230step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19230step1 raw19230step1Labels = mixedMoment B raw19230step2 raw19230step2Labels := by
      have ha : raw19230step2 = raw19230step1 := by apply Matrix.ext; unfold raw19230step2 raw19230step1; decide +kernel
      have hl : raw19230step1Labels = labelEmbedding1 ∘ raw19230step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19230step1 raw19230step1Labels raw19230step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw19231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19231Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw19231step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19231step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19231step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19231step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19231step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19231 raw19231Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw19231 raw19231Labels = mixedMoment B raw19231step0 raw19231step0Labels := by
      have hz : ∀ j, raw19231 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19231step0 = (fun i j => raw19231 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19231step0 raw19231; decide +kernel
      have hl : raw19231step0Labels = raw19231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19231 raw19231Labels permutation590 hz
    mixedMoment B raw19231step0 raw19231step0Labels = mixedMoment B raw19231step1 raw19231step1Labels := by
      have ha : raw19231step1 = (fun i j => raw19231step0 (permutation39 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19231step1 raw19231step0; decide +kernel
      have hl : raw19231step1Labels = raw19231step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19231step0 raw19231step0Labels permutation39 permutation7
    mixedMoment B raw19231step1 raw19231step1Labels = mixedMoment B raw19231step2 raw19231step2Labels := by
      have ha : raw19231step2 = -raw19231step1 := by apply Matrix.ext; change ∀ i j, raw19231step2 i j = -(raw19231step1 i j); unfold raw19231step2 raw19231step1; decide +kernel
      have hl : raw19231step2Labels = raw19231step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19231step2 raw19231step2Labels = mixedMoment B raw19231step3 raw19231step3Labels := by
      have ha : raw19231step3 = raw19231step2 := by apply Matrix.ext; unfold raw19231step3 raw19231step2; decide +kernel
      have hl : raw19231step2Labels = labelEmbedding1 ∘ raw19231step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19231step2 raw19231step2Labels raw19231step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw19232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19232Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw19232step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19232step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19232step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19232step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw19232step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19232 raw19232Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw19232 raw19232Labels = mixedMoment B raw19232step0 raw19232step0Labels := by
      have ha : raw19232step0 = (fun i j => raw19232 (permutation272 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19232step0 raw19232; decide +kernel
      have hl : raw19232step0Labels = raw19232Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19232 raw19232Labels permutation272 permutation5
    mixedMoment B raw19232step0 raw19232step0Labels = mixedMoment B raw19232step1 raw19232step1Labels := by
      have ha : raw19232step1 = -raw19232step0 := by apply Matrix.ext; change ∀ i j, raw19232step1 i j = -(raw19232step0 i j); unfold raw19232step1 raw19232step0; decide +kernel
      have hl : raw19232step1Labels = raw19232step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19232step1 raw19232step1Labels = mixedMoment B raw19232step2 raw19232step2Labels := by
      have ha : raw19232step2 = raw19232step1 := by apply Matrix.ext; unfold raw19232step2 raw19232step1; decide +kernel
      have hl : raw19232step1Labels = labelEmbedding1 ∘ raw19232step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19232step1 raw19232step1Labels raw19232step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw19233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19233Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19233step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19233step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19233step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19233step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19233step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19233step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19233 raw19233Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw19233 raw19233Labels = mixedMoment B raw19233step0 raw19233step0Labels := by
      have ha : raw19233step0 = (fun i j => raw19233 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19233step0 raw19233; decide +kernel
      have hl : raw19233step0Labels = raw19233Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19233 raw19233Labels permutation194 permutation7
    mixedMoment B raw19233step0 raw19233step0Labels = mixedMoment B raw19233step1 raw19233step1Labels := by
      have ha : raw19233step1 = -raw19233step0 := by apply Matrix.ext; change ∀ i j, raw19233step1 i j = -(raw19233step0 i j); unfold raw19233step1 raw19233step0; decide +kernel
      have hl : raw19233step1Labels = raw19233step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19233step1 raw19233step1Labels = mixedMoment B raw19233step2 raw19233step2Labels := by
      have ha : raw19233step2 = raw19233step1 := by apply Matrix.ext; unfold raw19233step2 raw19233step1; decide +kernel
      have hl : raw19233step1Labels = labelEmbedding1 ∘ raw19233step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19233step1 raw19233step1Labels raw19233step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

def raw19234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw19234Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19234step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw19234step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19234step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw19234step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19234step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw19234step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19234 raw19234Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw19234 raw19234Labels = mixedMoment B raw19234step0 raw19234step0Labels := by
      have ha : raw19234step0 = (fun i j => raw19234 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19234step0 raw19234; decide +kernel
      have hl : raw19234step0Labels = raw19234Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19234 raw19234Labels permutation194 permutation7
    mixedMoment B raw19234step0 raw19234step0Labels = mixedMoment B raw19234step1 raw19234step1Labels := by
      have ha : raw19234step1 = -raw19234step0 := by apply Matrix.ext; change ∀ i j, raw19234step1 i j = -(raw19234step0 i j); unfold raw19234step1 raw19234step0; decide +kernel
      have hl : raw19234step1Labels = raw19234step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19234step1 raw19234step1Labels = mixedMoment B raw19234step2 raw19234step2Labels := by
      have ha : raw19234step2 = raw19234step1 := by apply Matrix.ext; unfold raw19234step2 raw19234step1; decide +kernel
      have hl : raw19234step1Labels = labelEmbedding1 ∘ raw19234step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19234step1 raw19234step1Labels raw19234step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw19235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw19235Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19235step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19235step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19235step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19235step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19235step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19235step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19235 raw19235Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw19235 raw19235Labels = mixedMoment B raw19235step0 raw19235step0Labels := by
      have hz : ∀ j, raw19235 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19235step0 = (fun i j => raw19235 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19235step0 raw19235; decide +kernel
      have hl : raw19235step0Labels = raw19235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19235 raw19235Labels permutation590 hz
    mixedMoment B raw19235step0 raw19235step0Labels = mixedMoment B raw19235step1 raw19235step1Labels := by
      have ha : raw19235step1 = (fun i j => raw19235step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19235step1 raw19235step0; decide +kernel
      have hl : raw19235step1Labels = raw19235step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19235step0 raw19235step0Labels permutation38 permutation7
    mixedMoment B raw19235step1 raw19235step1Labels = mixedMoment B raw19235step2 raw19235step2Labels := by
      have ha : raw19235step2 = -raw19235step1 := by apply Matrix.ext; change ∀ i j, raw19235step2 i j = -(raw19235step1 i j); unfold raw19235step2 raw19235step1; decide +kernel
      have hl : raw19235step2Labels = raw19235step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19235step2 raw19235step2Labels = mixedMoment B raw19235step3 raw19235step3Labels := by
      have ha : raw19235step3 = raw19235step2 := by apply Matrix.ext; unfold raw19235step3 raw19235step2; decide +kernel
      have hl : raw19235step2Labels = labelEmbedding1 ∘ raw19235step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19235step2 raw19235step2Labels raw19235step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw19236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19236Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw19236step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19236step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw19236step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19236step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw19236step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19236 raw19236Labels = mixedMoment B node2661 node2661Labels := by
  calc
    mixedMoment B raw19236 raw19236Labels = mixedMoment B raw19236step0 raw19236step0Labels := by
      have ha : raw19236step0 = (fun i j => raw19236 (permutation273 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19236step0 raw19236; decide +kernel
      have hl : raw19236step0Labels = raw19236Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19236 raw19236Labels permutation273 permutation5
    mixedMoment B raw19236step0 raw19236step0Labels = mixedMoment B raw19236step1 raw19236step1Labels := by
      have ha : raw19236step1 = -raw19236step0 := by apply Matrix.ext; change ∀ i j, raw19236step1 i j = -(raw19236step0 i j); unfold raw19236step1 raw19236step0; decide +kernel
      have hl : raw19236step1Labels = raw19236step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19236step1 raw19236step1Labels = mixedMoment B raw19236step2 raw19236step2Labels := by
      have ha : raw19236step2 = raw19236step1 := by apply Matrix.ext; unfold raw19236step2 raw19236step1; decide +kernel
      have hl : raw19236step1Labels = labelEmbedding1 ∘ raw19236step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19236step1 raw19236step1Labels raw19236step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2661 node2661Labels := by rfl

def raw19237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19237Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19237step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19237step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19237step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19237step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19237step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19237 raw19237Labels = mixedMoment B node3810 node3810Labels := by
  calc
    mixedMoment B raw19237 raw19237Labels = mixedMoment B raw19237step0 raw19237step0Labels := by
      have ha : raw19237step0 = (fun i j => raw19237 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19237step0 raw19237; decide +kernel
      have hl : raw19237step0Labels = raw19237Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19237 raw19237Labels permutation194 permutation7
    mixedMoment B raw19237step0 raw19237step0Labels = mixedMoment B raw19237step1 raw19237step1Labels := by
      have ha : raw19237step1 = -raw19237step0 := by apply Matrix.ext; change ∀ i j, raw19237step1 i j = -(raw19237step0 i j); unfold raw19237step1 raw19237step0; decide +kernel
      have hl : raw19237step1Labels = raw19237step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19237step1 raw19237step1Labels = mixedMoment B raw19237step2 raw19237step2Labels := by
      have ha : raw19237step2 = raw19237step1 := by apply Matrix.ext; unfold raw19237step2 raw19237step1; decide +kernel
      have hl : raw19237step1Labels = labelEmbedding1 ∘ raw19237step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19237step1 raw19237step1Labels raw19237step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3810 node3810Labels := by rfl

def raw19238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19238Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw19238step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19238step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw19238step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19238 raw19238Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw19238 raw19238Labels = mixedMoment B raw19238step0 raw19238step0Labels := by
      have ha : raw19238step0 = (fun i j => raw19238 (permutation642 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19238step0 raw19238; decide +kernel
      have hl : raw19238step0Labels = raw19238Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19238 raw19238Labels permutation642 permutation5
    mixedMoment B raw19238step0 raw19238step0Labels = mixedMoment B raw19238step1 raw19238step1Labels := by
      have ha : raw19238step1 = raw19238step0 := by apply Matrix.ext; unfold raw19238step1 raw19238step0; decide +kernel
      have hl : raw19238step0Labels = labelEmbedding1 ∘ raw19238step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19238step0 raw19238step0Labels raw19238step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw19239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw19239Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw19239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw19239step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw19239step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw19239step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19239 raw19239Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw19239 raw19239Labels = mixedMoment B raw19239step0 raw19239step0Labels := by
      have ha : raw19239step0 = (fun i j => raw19239 (permutation636 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19239step0 raw19239; decide +kernel
      have hl : raw19239step0Labels = raw19239Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19239 raw19239Labels permutation636 permutation5
    mixedMoment B raw19239step0 raw19239step0Labels = mixedMoment B raw19239step1 raw19239step1Labels := by
      have ha : raw19239step1 = raw19239step0 := by apply Matrix.ext; unfold raw19239step1 raw19239step0; decide +kernel
      have hl : raw19239step0Labels = labelEmbedding1 ∘ raw19239step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19239step0 raw19239step0Labels raw19239step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw19240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19240 raw19240Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw19240 raw19240Labels = mixedMoment B raw19240step0 raw19240step0Labels := by
      have ha : raw19240step0 = (fun i j => raw19240 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19240step0 raw19240; decide +kernel
      have hl : raw19240step0Labels = raw19240Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19240 raw19240Labels permutation265 permutation2
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw19241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19241step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19241step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19241step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19241step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19241step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19241 raw19241Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw19241 raw19241Labels = mixedMoment B raw19241step0 raw19241step0Labels := by
      have ha : raw19241step0 = (fun i j => raw19241 (permutation361 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19241step0 raw19241; decide +kernel
      have hl : raw19241step0Labels = raw19241Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19241 raw19241Labels permutation361 permutation5
    mixedMoment B raw19241step0 raw19241step0Labels = mixedMoment B raw19241step1 raw19241step1Labels := by
      have ha : raw19241step1 = -raw19241step0 := by apply Matrix.ext; change ∀ i j, raw19241step1 i j = -(raw19241step0 i j); unfold raw19241step1 raw19241step0; decide +kernel
      have hl : raw19241step1Labels = raw19241step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19241step1 raw19241step1Labels = mixedMoment B raw19241step2 raw19241step2Labels := by
      have ha : raw19241step2 = raw19241step1 := by apply Matrix.ext; unfold raw19241step2 raw19241step1; decide +kernel
      have hl : raw19241step1Labels = labelEmbedding8 ∘ raw19241step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19241step1 raw19241step1Labels raw19241step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

def raw19242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19242step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19242step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19242step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19242step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19242step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19242 raw19242Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw19242 raw19242Labels = mixedMoment B raw19242step0 raw19242step0Labels := by
      have hz : ∀ j, raw19242 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19242step0 = (fun i j => raw19242 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19242step0 raw19242; decide +kernel
      have hl : raw19242step0Labels = raw19242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19242 raw19242Labels permutation434 hz
    mixedMoment B raw19242step0 raw19242step0Labels = mixedMoment B raw19242step1 raw19242step1Labels := by
      have ha : raw19242step1 = (fun i j => raw19242step0 (permutation69 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19242step1 raw19242step0; decide +kernel
      have hl : raw19242step1Labels = raw19242step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19242step0 raw19242step0Labels permutation69 permutation6
    mixedMoment B raw19242step1 raw19242step1Labels = mixedMoment B raw19242step2 raw19242step2Labels := by
      have ha : raw19242step2 = -raw19242step1 := by apply Matrix.ext; change ∀ i j, raw19242step2 i j = -(raw19242step1 i j); unfold raw19242step2 raw19242step1; decide +kernel
      have hl : raw19242step2Labels = raw19242step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19242step2 raw19242step2Labels = mixedMoment B raw19242step3 raw19242step3Labels := by
      have ha : raw19242step3 = raw19242step2 := by apply Matrix.ext; unfold raw19242step3 raw19242step2; decide +kernel
      have hl : raw19242step2Labels = labelEmbedding9 ∘ raw19242step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19242step2 raw19242step2Labels raw19242step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw19243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19243step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19243step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19243step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19243step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19243 raw19243Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw19243 raw19243Labels = mixedMoment B raw19243step0 raw19243step0Labels := by
      have hz : ∀ j, raw19243 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19243step0 = (fun i j => raw19243 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19243step0 raw19243; decide +kernel
      have hl : raw19243step0Labels = raw19243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19243 raw19243Labels permutation520 hz
    mixedMoment B raw19243step0 raw19243step0Labels = mixedMoment B raw19243step1 raw19243step1Labels := by
      have ha : raw19243step1 = (fun i j => raw19243step0 (permutation69 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19243step1 raw19243step0; decide +kernel
      have hl : raw19243step1Labels = raw19243step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19243step0 raw19243step0Labels permutation69 permutation6
    mixedMoment B raw19243step1 raw19243step1Labels = mixedMoment B raw19243step2 raw19243step2Labels := by
      have ha : raw19243step2 = -raw19243step1 := by apply Matrix.ext; change ∀ i j, raw19243step2 i j = -(raw19243step1 i j); unfold raw19243step2 raw19243step1; decide +kernel
      have hl : raw19243step2Labels = raw19243step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19243step2 raw19243step2Labels = mixedMoment B raw19243step3 raw19243step3Labels := by
      have ha : raw19243step3 = raw19243step2 := by apply Matrix.ext; unfold raw19243step3 raw19243step2; decide +kernel
      have hl : raw19243step2Labels = labelEmbedding9 ∘ raw19243step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19243step2 raw19243step2Labels raw19243step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw19244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19244step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19244step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19244step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19244step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19244step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19244 raw19244Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw19244 raw19244Labels = mixedMoment B raw19244step0 raw19244step0Labels := by
      have ha : raw19244step0 = (fun i j => raw19244 (permutation313 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19244step0 raw19244; decide +kernel
      have hl : raw19244step0Labels = raw19244Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19244 raw19244Labels permutation313 permutation6
    mixedMoment B raw19244step0 raw19244step0Labels = mixedMoment B raw19244step1 raw19244step1Labels := by
      have ha : raw19244step1 = -raw19244step0 := by apply Matrix.ext; change ∀ i j, raw19244step1 i j = -(raw19244step0 i j); unfold raw19244step1 raw19244step0; decide +kernel
      have hl : raw19244step1Labels = raw19244step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19244step1 raw19244step1Labels = mixedMoment B raw19244step2 raw19244step2Labels := by
      have ha : raw19244step2 = raw19244step1 := by apply Matrix.ext; unfold raw19244step2 raw19244step1; decide +kernel
      have hl : raw19244step1Labels = labelEmbedding9 ∘ raw19244step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19244step1 raw19244step1Labels raw19244step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

def raw19245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19245step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw19245step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19245step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19245step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19245step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19245step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19245 raw19245Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw19245 raw19245Labels = mixedMoment B raw19245step0 raw19245step0Labels := by
      have ha : raw19245step0 = (fun i j => raw19245 (permutation197 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19245step0 raw19245; decide +kernel
      have hl : raw19245step0Labels = raw19245Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19245 raw19245Labels permutation197 permutation5
    mixedMoment B raw19245step0 raw19245step0Labels = mixedMoment B raw19245step1 raw19245step1Labels := by
      have ha : raw19245step1 = -raw19245step0 := by apply Matrix.ext; change ∀ i j, raw19245step1 i j = -(raw19245step0 i j); unfold raw19245step1 raw19245step0; decide +kernel
      have hl : raw19245step1Labels = raw19245step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19245step1 raw19245step1Labels = mixedMoment B raw19245step2 raw19245step2Labels := by
      have ha : raw19245step2 = raw19245step1 := by apply Matrix.ext; unfold raw19245step2 raw19245step1; decide +kernel
      have hl : raw19245step1Labels = labelEmbedding8 ∘ raw19245step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19245step1 raw19245step1Labels raw19245step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

def raw19246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw19246step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19246step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19246step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19246step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19246step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19246 raw19246Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw19246 raw19246Labels = mixedMoment B raw19246step0 raw19246step0Labels := by
      have ha : raw19246step0 = (fun i j => raw19246 (permutation197 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19246step0 raw19246; decide +kernel
      have hl : raw19246step0Labels = raw19246Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19246 raw19246Labels permutation197 permutation5
    mixedMoment B raw19246step0 raw19246step0Labels = mixedMoment B raw19246step1 raw19246step1Labels := by
      have ha : raw19246step1 = -raw19246step0 := by apply Matrix.ext; change ∀ i j, raw19246step1 i j = -(raw19246step0 i j); unfold raw19246step1 raw19246step0; decide +kernel
      have hl : raw19246step1Labels = raw19246step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19246step1 raw19246step1Labels = mixedMoment B raw19246step2 raw19246step2Labels := by
      have ha : raw19246step2 = raw19246step1 := by apply Matrix.ext; unfold raw19246step2 raw19246step1; decide +kernel
      have hl : raw19246step1Labels = labelEmbedding8 ∘ raw19246step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19246step1 raw19246step1Labels raw19246step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5354 node5354Labels := by rfl

def raw19247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19247step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19247step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19247step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19247 raw19247Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw19247 raw19247Labels = mixedMoment B raw19247step0 raw19247step0Labels := by
      have hz : ∀ j, raw19247 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19247step0 = (fun i j => raw19247 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19247step0 raw19247; decide +kernel
      have hl : raw19247step0Labels = raw19247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19247 raw19247Labels permutation434 hz
    mixedMoment B raw19247step0 raw19247step0Labels = mixedMoment B raw19247step1 raw19247step1Labels := by
      have ha : raw19247step1 = (fun i j => raw19247step0 (permutation73 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19247step1 raw19247step0; decide +kernel
      have hl : raw19247step1Labels = raw19247step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19247step0 raw19247step0Labels permutation73 permutation4
    mixedMoment B raw19247step1 raw19247step1Labels = mixedMoment B raw19247step2 raw19247step2Labels := by
      have ha : raw19247step2 = raw19247step1 := by apply Matrix.ext; unfold raw19247step2 raw19247step1; decide +kernel
      have hl : raw19247step1Labels = labelEmbedding7 ∘ raw19247step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19247step1 raw19247step1Labels raw19247step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw19248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19248step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19248step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19248step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19248 raw19248Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw19248 raw19248Labels = mixedMoment B raw19248step0 raw19248step0Labels := by
      have hz : ∀ j, raw19248 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19248step0 = (fun i j => raw19248 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19248step0 raw19248; decide +kernel
      have hl : raw19248step0Labels = raw19248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19248 raw19248Labels permutation520 hz
    mixedMoment B raw19248step0 raw19248step0Labels = mixedMoment B raw19248step1 raw19248step1Labels := by
      have ha : raw19248step1 = (fun i j => raw19248step0 (permutation73 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19248step1 raw19248step0; decide +kernel
      have hl : raw19248step1Labels = raw19248step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19248step0 raw19248step0Labels permutation73 permutation4
    mixedMoment B raw19248step1 raw19248step1Labels = mixedMoment B raw19248step2 raw19248step2Labels := by
      have ha : raw19248step2 = raw19248step1 := by apply Matrix.ext; unfold raw19248step2 raw19248step1; decide +kernel
      have hl : raw19248step1Labels = labelEmbedding7 ∘ raw19248step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19248step1 raw19248step1Labels raw19248step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw19249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19249step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19249step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19249step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw19249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19249 raw19249Labels = mixedMoment B node5417 node5417Labels := by
  calc
    mixedMoment B raw19249 raw19249Labels = mixedMoment B raw19249step0 raw19249step0Labels := by
      have ha : raw19249step0 = (fun i j => raw19249 (permutation316 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19249step0 raw19249; decide +kernel
      have hl : raw19249step0Labels = raw19249Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19249 raw19249Labels permutation316 permutation4
    mixedMoment B raw19249step0 raw19249step0Labels = mixedMoment B raw19249step1 raw19249step1Labels := by
      have ha : raw19249step1 = raw19249step0 := by apply Matrix.ext; unfold raw19249step1 raw19249step0; decide +kernel
      have hl : raw19249step0Labels = labelEmbedding7 ∘ raw19249step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19249step0 raw19249step0Labels raw19249step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5417 node5417Labels := by rfl

def raw19250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19250step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19250step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19250step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19250 raw19250Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw19250 raw19250Labels = mixedMoment B raw19250step0 raw19250step0Labels := by
      have ha : raw19250step0 = (fun i j => raw19250 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19250step0 raw19250; decide +kernel
      have hl : raw19250step0Labels = raw19250Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19250 raw19250Labels permutation156 permutation3
    mixedMoment B raw19250step0 raw19250step0Labels = mixedMoment B raw19250step1 raw19250step1Labels := by
      have ha : raw19250step1 = raw19250step0 := by apply Matrix.ext; unfold raw19250step1 raw19250step0; decide +kernel
      have hl : raw19250step0Labels = labelEmbedding6 ∘ raw19250step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19250step0 raw19250step0Labels raw19250step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

def raw19251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19251 raw19251Labels = mixedMoment B node5386 node5386Labels := by
  calc
    mixedMoment B raw19251 raw19251Labels = mixedMoment B raw19251step0 raw19251step0Labels := by
      have ha : raw19251step0 = (fun i j => raw19251 (permutation273 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19251step0 raw19251; decide +kernel
      have hl : raw19251step0Labels = raw19251Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19251 raw19251Labels permutation273 permutation2
    _ = mixedMoment B node5386 node5386Labels := by rfl

def raw19252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19252step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19252step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19252 raw19252Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw19252 raw19252Labels = mixedMoment B raw19252step0 raw19252step0Labels := by
      have hz : ∀ j, raw19252 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19252step0 = (fun i j => raw19252 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19252step0 raw19252; decide +kernel
      have hl : raw19252step0Labels = raw19252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19252 raw19252Labels permutation434 hz
    mixedMoment B raw19252step0 raw19252step0Labels = mixedMoment B raw19252step1 raw19252step1Labels := by
      have ha : raw19252step1 = (fun i j => raw19252step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19252step1 raw19252step0; decide +kernel
      have hl : raw19252step1Labels = raw19252step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19252step0 raw19252step0Labels permutation33 permutation3
    mixedMoment B raw19252step1 raw19252step1Labels = mixedMoment B raw19252step2 raw19252step2Labels := by
      have ha : raw19252step2 = raw19252step1 := by apply Matrix.ext; unfold raw19252step2 raw19252step1; decide +kernel
      have hl : raw19252step1Labels = labelEmbedding6 ∘ raw19252step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19252step1 raw19252step1Labels raw19252step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw19253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19253step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19253step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19253 raw19253Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw19253 raw19253Labels = mixedMoment B raw19253step0 raw19253step0Labels := by
      have hz : ∀ j, raw19253 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19253step0 = (fun i j => raw19253 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19253step0 raw19253; decide +kernel
      have hl : raw19253step0Labels = raw19253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19253 raw19253Labels permutation520 hz
    mixedMoment B raw19253step0 raw19253step0Labels = mixedMoment B raw19253step1 raw19253step1Labels := by
      have ha : raw19253step1 = (fun i j => raw19253step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19253step1 raw19253step0; decide +kernel
      have hl : raw19253step1Labels = raw19253step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19253step0 raw19253step0Labels permutation33 permutation3
    mixedMoment B raw19253step1 raw19253step1Labels = mixedMoment B raw19253step2 raw19253step2Labels := by
      have ha : raw19253step2 = raw19253step1 := by apply Matrix.ext; unfold raw19253step2 raw19253step1; decide +kernel
      have hl : raw19253step1Labels = labelEmbedding6 ∘ raw19253step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19253step1 raw19253step1Labels raw19253step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw19254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19254step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19254step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19254step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19254step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19254 raw19254Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw19254 raw19254Labels = mixedMoment B raw19254step0 raw19254step0Labels := by
      have ha : raw19254step0 = (fun i j => raw19254 (permutation252 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19254step0 raw19254; decide +kernel
      have hl : raw19254step0Labels = raw19254Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19254 raw19254Labels permutation252 permutation5
    mixedMoment B raw19254step0 raw19254step0Labels = mixedMoment B raw19254step1 raw19254step1Labels := by
      have ha : raw19254step1 = -raw19254step0 := by apply Matrix.ext; change ∀ i j, raw19254step1 i j = -(raw19254step0 i j); unfold raw19254step1 raw19254step0; decide +kernel
      have hl : raw19254step1Labels = raw19254step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19254step1 raw19254step1Labels = mixedMoment B raw19254step2 raw19254step2Labels := by
      have ha : raw19254step2 = raw19254step1 := by apply Matrix.ext; unfold raw19254step2 raw19254step1; decide +kernel
      have hl : raw19254step1Labels = labelEmbedding8 ∘ raw19254step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19254step1 raw19254step1Labels raw19254step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw19255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw19255step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19255step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19255step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19255step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19255step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19255 raw19255Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw19255 raw19255Labels = mixedMoment B raw19255step0 raw19255step0Labels := by
      have ha : raw19255step0 = (fun i j => raw19255 (permutation195 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19255step0 raw19255; decide +kernel
      have hl : raw19255step0Labels = raw19255Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19255 raw19255Labels permutation195 permutation5
    mixedMoment B raw19255step0 raw19255step0Labels = mixedMoment B raw19255step1 raw19255step1Labels := by
      have ha : raw19255step1 = -raw19255step0 := by apply Matrix.ext; change ∀ i j, raw19255step1 i j = -(raw19255step0 i j); unfold raw19255step1 raw19255step0; decide +kernel
      have hl : raw19255step1Labels = raw19255step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19255step1 raw19255step1Labels = mixedMoment B raw19255step2 raw19255step2Labels := by
      have ha : raw19255step2 = raw19255step1 := by apply Matrix.ext; unfold raw19255step2 raw19255step1; decide +kernel
      have hl : raw19255step1Labels = labelEmbedding8 ∘ raw19255step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19255step1 raw19255step1Labels raw19255step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

def raw19256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19256step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19256step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19256step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19256 raw19256Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw19256 raw19256Labels = mixedMoment B raw19256step0 raw19256step0Labels := by
      have ha : raw19256step0 = (fun i j => raw19256 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19256step0 raw19256; decide +kernel
      have hl : raw19256step0Labels = raw19256Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19256 raw19256Labels permutation157 permutation3
    mixedMoment B raw19256step0 raw19256step0Labels = mixedMoment B raw19256step1 raw19256step1Labels := by
      have ha : raw19256step1 = raw19256step0 := by apply Matrix.ext; unfold raw19256step1 raw19256step0; decide +kernel
      have hl : raw19256step0Labels = labelEmbedding6 ∘ raw19256step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19256step0 raw19256step0Labels raw19256step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw19257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw19257step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19257step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19257step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19257step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19257step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19257 raw19257Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw19257 raw19257Labels = mixedMoment B raw19257step0 raw19257step0Labels := by
      have ha : raw19257step0 = (fun i j => raw19257 (permutation195 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19257step0 raw19257; decide +kernel
      have hl : raw19257step0Labels = raw19257Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19257 raw19257Labels permutation195 permutation5
    mixedMoment B raw19257step0 raw19257step0Labels = mixedMoment B raw19257step1 raw19257step1Labels := by
      have ha : raw19257step1 = -raw19257step0 := by apply Matrix.ext; change ∀ i j, raw19257step1 i j = -(raw19257step0 i j); unfold raw19257step1 raw19257step0; decide +kernel
      have hl : raw19257step1Labels = raw19257step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19257step1 raw19257step1Labels = mixedMoment B raw19257step2 raw19257step2Labels := by
      have ha : raw19257step2 = raw19257step1 := by apply Matrix.ext; unfold raw19257step2 raw19257step1; decide +kernel
      have hl : raw19257step1Labels = labelEmbedding8 ∘ raw19257step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19257step1 raw19257step1Labels raw19257step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

def raw19258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw19258step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw19258step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19258step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19258step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19258step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19258 raw19258Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw19258 raw19258Labels = mixedMoment B raw19258step0 raw19258step0Labels := by
      have hz : ∀ j, raw19258 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19258step0 = (fun i j => raw19258 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19258step0 raw19258; decide +kernel
      have hl : raw19258step0Labels = raw19258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19258 raw19258Labels permutation520 hz
    mixedMoment B raw19258step0 raw19258step0Labels = mixedMoment B raw19258step1 raw19258step1Labels := by
      have ha : raw19258step1 = (fun i j => raw19258step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19258step1 raw19258step0; decide +kernel
      have hl : raw19258step1Labels = raw19258step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19258step0 raw19258step0Labels permutation127 permutation3
    mixedMoment B raw19258step1 raw19258step1Labels = mixedMoment B raw19258step2 raw19258step2Labels := by
      have ha : raw19258step2 = -raw19258step1 := by apply Matrix.ext; change ∀ i j, raw19258step2 i j = -(raw19258step1 i j); unfold raw19258step2 raw19258step1; decide +kernel
      have hl : raw19258step2Labels = raw19258step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19258step2 raw19258step2Labels = mixedMoment B raw19258step3 raw19258step3Labels := by
      have ha : raw19258step3 = raw19258step2 := by apply Matrix.ext; unfold raw19258step3 raw19258step2; decide +kernel
      have hl : raw19258step2Labels = labelEmbedding6 ∘ raw19258step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19258step2 raw19258step2Labels raw19258step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw19259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19259step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19259step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19259 raw19259Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw19259 raw19259Labels = mixedMoment B raw19259step0 raw19259step0Labels := by
      have ha : raw19259step0 = (fun i j => raw19259 (permutation492 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19259step0 raw19259; decide +kernel
      have hl : raw19259step0Labels = raw19259Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19259 raw19259Labels permutation492 permutation5
    mixedMoment B raw19259step0 raw19259step0Labels = mixedMoment B raw19259step1 raw19259step1Labels := by
      have ha : raw19259step1 = raw19259step0 := by apply Matrix.ext; unfold raw19259step1 raw19259step0; decide +kernel
      have hl : raw19259step0Labels = labelEmbedding8 ∘ raw19259step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19259step0 raw19259step0Labels raw19259step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5400 node5400Labels := by rfl

def raw19260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw19260step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19260step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19260step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19260step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19260step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19260 raw19260Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw19260 raw19260Labels = mixedMoment B raw19260step0 raw19260step0Labels := by
      have ha : raw19260step0 = (fun i j => raw19260 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19260step0 raw19260; decide +kernel
      have hl : raw19260step0Labels = raw19260Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19260 raw19260Labels permutation194 permutation5
    mixedMoment B raw19260step0 raw19260step0Labels = mixedMoment B raw19260step1 raw19260step1Labels := by
      have ha : raw19260step1 = -raw19260step0 := by apply Matrix.ext; change ∀ i j, raw19260step1 i j = -(raw19260step0 i j); unfold raw19260step1 raw19260step0; decide +kernel
      have hl : raw19260step1Labels = raw19260step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19260step1 raw19260step1Labels = mixedMoment B raw19260step2 raw19260step2Labels := by
      have ha : raw19260step2 = raw19260step1 := by apply Matrix.ext; unfold raw19260step2 raw19260step1; decide +kernel
      have hl : raw19260step1Labels = labelEmbedding8 ∘ raw19260step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19260step1 raw19260step1Labels raw19260step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

def raw19261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19261step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19261step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19261step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19261 raw19261Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw19261 raw19261Labels = mixedMoment B raw19261step0 raw19261step0Labels := by
      have ha : raw19261step0 = (fun i j => raw19261 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19261step0 raw19261; decide +kernel
      have hl : raw19261step0Labels = raw19261Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19261 raw19261Labels permutation156 permutation3
    mixedMoment B raw19261step0 raw19261step0Labels = mixedMoment B raw19261step1 raw19261step1Labels := by
      have ha : raw19261step1 = raw19261step0 := by apply Matrix.ext; unfold raw19261step1 raw19261step0; decide +kernel
      have hl : raw19261step0Labels = labelEmbedding6 ∘ raw19261step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19261step0 raw19261step0Labels raw19261step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw19262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw19262step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19262step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19262step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw19262step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19262 raw19262Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw19262 raw19262Labels = mixedMoment B raw19262step0 raw19262step0Labels := by
      have ha : raw19262step0 = (fun i j => raw19262 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19262step0 raw19262; decide +kernel
      have hl : raw19262step0Labels = raw19262Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19262 raw19262Labels permutation194 permutation5
    mixedMoment B raw19262step0 raw19262step0Labels = mixedMoment B raw19262step1 raw19262step1Labels := by
      have ha : raw19262step1 = -raw19262step0 := by apply Matrix.ext; change ∀ i j, raw19262step1 i j = -(raw19262step0 i j); unfold raw19262step1 raw19262step0; decide +kernel
      have hl : raw19262step1Labels = raw19262step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19262step1 raw19262step1Labels = mixedMoment B raw19262step2 raw19262step2Labels := by
      have ha : raw19262step2 = raw19262step1 := by apply Matrix.ext; unfold raw19262step2 raw19262step1; decide +kernel
      have hl : raw19262step1Labels = labelEmbedding8 ∘ raw19262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19262step1 raw19262step1Labels raw19262step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

def raw19263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw19263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw19263step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19263step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19263step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19263step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19263step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19263 raw19263Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw19263 raw19263Labels = mixedMoment B raw19263step0 raw19263step0Labels := by
      have hz : ∀ j, raw19263 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19263step0 = (fun i j => raw19263 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19263step0 raw19263; decide +kernel
      have hl : raw19263step0Labels = raw19263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19263 raw19263Labels permutation434 hz
    mixedMoment B raw19263step0 raw19263step0Labels = mixedMoment B raw19263step1 raw19263step1Labels := by
      have ha : raw19263step1 = (fun i j => raw19263step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19263step1 raw19263step0; decide +kernel
      have hl : raw19263step1Labels = raw19263step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19263step0 raw19263step0Labels permutation127 permutation3
    mixedMoment B raw19263step1 raw19263step1Labels = mixedMoment B raw19263step2 raw19263step2Labels := by
      have ha : raw19263step2 = -raw19263step1 := by apply Matrix.ext; change ∀ i j, raw19263step2 i j = -(raw19263step1 i j); unfold raw19263step2 raw19263step1; decide +kernel
      have hl : raw19263step2Labels = raw19263step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19263step2 raw19263step2Labels = mixedMoment B raw19263step3 raw19263step3Labels := by
      have ha : raw19263step3 = raw19263step2 := by apply Matrix.ext; unfold raw19263step3 raw19263step2; decide +kernel
      have hl : raw19263step2Labels = labelEmbedding6 ∘ raw19263step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19263step2 raw19263step2Labels raw19263step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw19264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw19264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19264step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw19264step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19264 raw19264Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw19264 raw19264Labels = mixedMoment B raw19264step0 raw19264step0Labels := by
      have ha : raw19264step0 = (fun i j => raw19264 (permutation557 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19264step0 raw19264; decide +kernel
      have hl : raw19264step0Labels = raw19264Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19264 raw19264Labels permutation557 permutation5
    mixedMoment B raw19264step0 raw19264step0Labels = mixedMoment B raw19264step1 raw19264step1Labels := by
      have ha : raw19264step1 = raw19264step0 := by apply Matrix.ext; unfold raw19264step1 raw19264step0; decide +kernel
      have hl : raw19264step0Labels = labelEmbedding8 ∘ raw19264step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19264step0 raw19264step0Labels raw19264step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5400 node5400Labels := by rfl

def raw19265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19265step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw19265step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19265step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw19265step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19265 raw19265Labels = mixedMoment B node4826 node4826Labels := by
  calc
    mixedMoment B raw19265 raw19265Labels = mixedMoment B raw19265step0 raw19265step0Labels := by
      have ha : raw19265step0 = (fun i j => raw19265 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19265step0 raw19265; decide +kernel
      have hl : raw19265step0Labels = raw19265Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19265 raw19265Labels permutation176 permutation5
    mixedMoment B raw19265step0 raw19265step0Labels = mixedMoment B raw19265step1 raw19265step1Labels := by
      have ha : raw19265step1 = -raw19265step0 := by apply Matrix.ext; change ∀ i j, raw19265step1 i j = -(raw19265step0 i j); unfold raw19265step1 raw19265step0; decide +kernel
      have hl : raw19265step1Labels = raw19265step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19265step1 raw19265step1Labels = mixedMoment B raw19265step2 raw19265step2Labels := by
      have ha : raw19265step2 = raw19265step1 := by apply Matrix.ext; unfold raw19265step2 raw19265step1; decide +kernel
      have hl : raw19265step1Labels = labelEmbedding8 ∘ raw19265step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19265step1 raw19265step1Labels raw19265step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4826 node4826Labels := by rfl

def raw19266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19266step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19266step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19266step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19266 raw19266Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw19266 raw19266Labels = mixedMoment B raw19266step0 raw19266step0Labels := by
      have ha : raw19266step0 = (fun i j => raw19266 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19266step0 raw19266; decide +kernel
      have hl : raw19266step0Labels = raw19266Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19266 raw19266Labels permutation152 permutation3
    mixedMoment B raw19266step0 raw19266step0Labels = mixedMoment B raw19266step1 raw19266step1Labels := by
      have ha : raw19266step1 = raw19266step0 := by apply Matrix.ext; unfold raw19266step1 raw19266step0; decide +kernel
      have hl : raw19266step0Labels = labelEmbedding6 ∘ raw19266step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19266step0 raw19266step0Labels raw19266step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw19267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19267step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19267step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw19267step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19267step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw19267step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19267 raw19267Labels = mixedMoment B node5363 node5363Labels := by
  calc
    mixedMoment B raw19267 raw19267Labels = mixedMoment B raw19267step0 raw19267step0Labels := by
      have ha : raw19267step0 = (fun i j => raw19267 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19267step0 raw19267; decide +kernel
      have hl : raw19267step0Labels = raw19267Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19267 raw19267Labels permutation176 permutation5
    mixedMoment B raw19267step0 raw19267step0Labels = mixedMoment B raw19267step1 raw19267step1Labels := by
      have ha : raw19267step1 = -raw19267step0 := by apply Matrix.ext; change ∀ i j, raw19267step1 i j = -(raw19267step0 i j); unfold raw19267step1 raw19267step0; decide +kernel
      have hl : raw19267step1Labels = raw19267step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19267step1 raw19267step1Labels = mixedMoment B raw19267step2 raw19267step2Labels := by
      have ha : raw19267step2 = raw19267step1 := by apply Matrix.ext; unfold raw19267step2 raw19267step1; decide +kernel
      have hl : raw19267step1Labels = labelEmbedding8 ∘ raw19267step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19267step1 raw19267step1Labels raw19267step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5363 node5363Labels := by rfl

def raw19268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19268step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19268step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19268step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19268step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19268 raw19268Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw19268 raw19268Labels = mixedMoment B raw19268step0 raw19268step0Labels := by
      have hz : ∀ j, raw19268 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19268step0 = (fun i j => raw19268 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19268step0 raw19268; decide +kernel
      have hl : raw19268step0Labels = raw19268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19268 raw19268Labels permutation434 hz
    mixedMoment B raw19268step0 raw19268step0Labels = mixedMoment B raw19268step1 raw19268step1Labels := by
      have ha : raw19268step1 = (fun i j => raw19268step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19268step1 raw19268step0; decide +kernel
      have hl : raw19268step1Labels = raw19268step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19268step0 raw19268step0Labels permutation38 permutation5
    mixedMoment B raw19268step1 raw19268step1Labels = mixedMoment B raw19268step2 raw19268step2Labels := by
      have ha : raw19268step2 = -raw19268step1 := by apply Matrix.ext; change ∀ i j, raw19268step2 i j = -(raw19268step1 i j); unfold raw19268step2 raw19268step1; decide +kernel
      have hl : raw19268step2Labels = raw19268step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19268step2 raw19268step2Labels = mixedMoment B raw19268step3 raw19268step3Labels := by
      have ha : raw19268step3 = raw19268step2 := by apply Matrix.ext; unfold raw19268step3 raw19268step2; decide +kernel
      have hl : raw19268step2Labels = labelEmbedding8 ∘ raw19268step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19268step2 raw19268step2Labels raw19268step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw19269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw19269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19269step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw19269step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19269step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19269step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19269step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw19269step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19269 raw19269Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw19269 raw19269Labels = mixedMoment B raw19269step0 raw19269step0Labels := by
      have hz : ∀ j, raw19269 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19269step0 = (fun i j => raw19269 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19269step0 raw19269; decide +kernel
      have hl : raw19269step0Labels = raw19269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19269 raw19269Labels permutation520 hz
    mixedMoment B raw19269step0 raw19269step0Labels = mixedMoment B raw19269step1 raw19269step1Labels := by
      have ha : raw19269step1 = (fun i j => raw19269step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19269step1 raw19269step0; decide +kernel
      have hl : raw19269step1Labels = raw19269step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19269step0 raw19269step0Labels permutation38 permutation5
    mixedMoment B raw19269step1 raw19269step1Labels = mixedMoment B raw19269step2 raw19269step2Labels := by
      have ha : raw19269step2 = -raw19269step1 := by apply Matrix.ext; change ∀ i j, raw19269step2 i j = -(raw19269step1 i j); unfold raw19269step2 raw19269step1; decide +kernel
      have hl : raw19269step2Labels = raw19269step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19269step2 raw19269step2Labels = mixedMoment B raw19269step3 raw19269step3Labels := by
      have ha : raw19269step3 = raw19269step2 := by apply Matrix.ext; unfold raw19269step3 raw19269step2; decide +kernel
      have hl : raw19269step2Labels = labelEmbedding8 ∘ raw19269step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19269step2 raw19269step2Labels raw19269step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw19270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19270Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19270step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19270 raw19270Labels = mixedMoment B node4033 node4033Labels := by
  calc
    mixedMoment B raw19270 raw19270Labels = mixedMoment B raw19270step0 raw19270step0Labels := by
      have ha : raw19270step0 = (fun i j => raw19270 (permutation269 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19270step0 raw19270; decide +kernel
      have hl : raw19270step0Labels = raw19270Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19270 raw19270Labels permutation269 permutation3
    _ = mixedMoment B node4033 node4033Labels := by rfl

def raw19271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19271Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2]]
def raw19271step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19271step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw19271step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19271 raw19271Labels = mixedMoment B node4008 node4008Labels := by
  calc
    mixedMoment B raw19271 raw19271Labels = mixedMoment B raw19271step0 raw19271step0Labels := by
      have ha : raw19271step0 = (fun i j => raw19271 (permutation314 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19271step0 raw19271; decide +kernel
      have hl : raw19271step0Labels = raw19271Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19271 raw19271Labels permutation314 permutation6
    mixedMoment B raw19271step0 raw19271step0Labels = mixedMoment B raw19271step1 raw19271step1Labels := by
      have ha : raw19271step1 = -raw19271step0 := by apply Matrix.ext; change ∀ i j, raw19271step1 i j = -(raw19271step0 i j); unfold raw19271step1 raw19271step0; decide +kernel
      have hl : raw19271step1Labels = raw19271step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4008 node4008Labels := by rfl

def raw19272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19272Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19272step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19272step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19272 raw19272Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw19272 raw19272Labels = mixedMoment B raw19272step0 raw19272step0Labels := by
      have hz : ∀ j, raw19272 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19272step0 = (fun i j => raw19272 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19272step0 raw19272; decide +kernel
      have hl : raw19272step0Labels = raw19272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19272 raw19272Labels permutation434 hz
    mixedMoment B raw19272step0 raw19272step0Labels = mixedMoment B raw19272step1 raw19272step1Labels := by
      have ha : raw19272step1 = (fun i j => raw19272step0 (permutation69 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19272step1 raw19272step0; decide +kernel
      have hl : raw19272step1Labels = raw19272step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19272step0 raw19272step0Labels permutation69 permutation6
    mixedMoment B raw19272step1 raw19272step1Labels = mixedMoment B raw19272step2 raw19272step2Labels := by
      have ha : raw19272step2 = -raw19272step1 := by apply Matrix.ext; change ∀ i j, raw19272step2 i j = -(raw19272step1 i j); unfold raw19272step2 raw19272step1; decide +kernel
      have hl : raw19272step2Labels = raw19272step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw19273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19273Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19273step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19273step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19273step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19273 raw19273Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw19273 raw19273Labels = mixedMoment B raw19273step0 raw19273step0Labels := by
      have hz : ∀ j, raw19273 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19273step0 = (fun i j => raw19273 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19273step0 raw19273; decide +kernel
      have hl : raw19273step0Labels = raw19273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19273 raw19273Labels permutation520 hz
    mixedMoment B raw19273step0 raw19273step0Labels = mixedMoment B raw19273step1 raw19273step1Labels := by
      have ha : raw19273step1 = (fun i j => raw19273step0 (permutation69 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19273step1 raw19273step0; decide +kernel
      have hl : raw19273step1Labels = raw19273step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19273step0 raw19273step0Labels permutation69 permutation6
    mixedMoment B raw19273step1 raw19273step1Labels = mixedMoment B raw19273step2 raw19273step2Labels := by
      have ha : raw19273step2 = -raw19273step1 := by apply Matrix.ext; change ∀ i j, raw19273step2 i j = -(raw19273step1 i j); unfold raw19273step2 raw19273step1; decide +kernel
      have hl : raw19273step2Labels = raw19273step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw19274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19274Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19274step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19274step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19274 raw19274Labels = mixedMoment B node4009 node4009Labels := by
  calc
    mixedMoment B raw19274 raw19274Labels = mixedMoment B raw19274step0 raw19274step0Labels := by
      have ha : raw19274step0 = (fun i j => raw19274 (permutation313 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19274step0 raw19274; decide +kernel
      have hl : raw19274step0Labels = raw19274Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19274 raw19274Labels permutation313 permutation6
    mixedMoment B raw19274step0 raw19274step0Labels = mixedMoment B raw19274step1 raw19274step1Labels := by
      have ha : raw19274step1 = -raw19274step0 := by apply Matrix.ext; change ∀ i j, raw19274step1 i j = -(raw19274step0 i j); unfold raw19274step1 raw19274step0; decide +kernel
      have hl : raw19274step1Labels = raw19274step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4009 node4009Labels := by rfl

def raw19275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19275Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19275step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19275 raw19275Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw19275 raw19275Labels = mixedMoment B raw19275step0 raw19275step0Labels := by
      have ha : raw19275step0 = (fun i j => raw19275 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19275step0 raw19275; decide +kernel
      have hl : raw19275step0Labels = raw19275Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19275 raw19275Labels permutation180 permutation3
    _ = mixedMoment B node2214 node2214Labels := by rfl

def raw19276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19276Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19276step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19276 raw19276Labels = mixedMoment B node3769 node3769Labels := by
  calc
    mixedMoment B raw19276 raw19276Labels = mixedMoment B raw19276step0 raw19276step0Labels := by
      have ha : raw19276step0 = (fun i j => raw19276 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19276step0 raw19276; decide +kernel
      have hl : raw19276step0Labels = raw19276Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19276 raw19276Labels permutation180 permutation3
    _ = mixedMoment B node3769 node3769Labels := by rfl

def raw19277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19277Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19277step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw19277step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19277 raw19277Labels = mixedMoment B node3906 node3906Labels := by
  calc
    mixedMoment B raw19277 raw19277Labels = mixedMoment B raw19277step0 raw19277step0Labels := by
      have hz : ∀ j, raw19277 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19277step0 = (fun i j => raw19277 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19277step0 raw19277; decide +kernel
      have hl : raw19277step0Labels = raw19277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19277 raw19277Labels permutation434 hz
    mixedMoment B raw19277step0 raw19277step0Labels = mixedMoment B raw19277step1 raw19277step1Labels := by
      have ha : raw19277step1 = (fun i j => raw19277step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19277step1 raw19277step0; decide +kernel
      have hl : raw19277step1Labels = raw19277step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19277step0 raw19277step0Labels permutation39 permutation3
    _ = mixedMoment B node3906 node3906Labels := by rfl

def raw19278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19278Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19278step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw19278step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19278 raw19278Labels = mixedMoment B node3906 node3906Labels := by
  calc
    mixedMoment B raw19278 raw19278Labels = mixedMoment B raw19278step0 raw19278step0Labels := by
      have hz : ∀ j, raw19278 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19278step0 = (fun i j => raw19278 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19278step0 raw19278; decide +kernel
      have hl : raw19278step0Labels = raw19278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19278 raw19278Labels permutation520 hz
    mixedMoment B raw19278step0 raw19278step0Labels = mixedMoment B raw19278step1 raw19278step1Labels := by
      have ha : raw19278step1 = (fun i j => raw19278step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19278step1 raw19278step0; decide +kernel
      have hl : raw19278step1Labels = raw19278step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19278step0 raw19278step0Labels permutation39 permutation3
    _ = mixedMoment B node3906 node3906Labels := by rfl

def raw19279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19279Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1]]
def raw19279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19279 raw19279Labels = mixedMoment B node3897 node3897Labels := by
  calc
    mixedMoment B raw19279 raw19279Labels = mixedMoment B raw19279step0 raw19279step0Labels := by
      have ha : raw19279step0 = (fun i j => raw19279 (permutation194 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19279step0 raw19279; decide +kernel
      have hl : raw19279step0Labels = raw19279Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19279 raw19279Labels permutation194 permutation3
    _ = mixedMoment B node3897 node3897Labels := by rfl

def raw19280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19280Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19280step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19280 raw19280Labels = mixedMoment B node2105 node2105Labels := by
  calc
    mixedMoment B raw19280 raw19280Labels = mixedMoment B raw19280step0 raw19280step0Labels := by
      have ha : raw19280step0 = (fun i j => raw19280 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19280step0 raw19280; decide +kernel
      have hl : raw19280step0Labels = raw19280Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19280 raw19280Labels permutation156 permutation3
    _ = mixedMoment B node2105 node2105Labels := by rfl

def raw19281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19281Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19281step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19281 raw19281Labels = mixedMoment B node3735 node3735Labels := by
  calc
    mixedMoment B raw19281 raw19281Labels = mixedMoment B raw19281step0 raw19281step0Labels := by
      have ha : raw19281step0 = (fun i j => raw19281 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19281step0 raw19281; decide +kernel
      have hl : raw19281step0Labels = raw19281Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19281 raw19281Labels permutation156 permutation3
    _ = mixedMoment B node3735 node3735Labels := by rfl

def raw19282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19282Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19282step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19282step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19282 raw19282Labels = mixedMoment B node3887 node3887Labels := by
  calc
    mixedMoment B raw19282 raw19282Labels = mixedMoment B raw19282step0 raw19282step0Labels := by
      have hz : ∀ j, raw19282 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19282step0 = (fun i j => raw19282 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19282step0 raw19282; decide +kernel
      have hl : raw19282step0Labels = raw19282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19282 raw19282Labels permutation434 hz
    mixedMoment B raw19282step0 raw19282step0Labels = mixedMoment B raw19282step1 raw19282step1Labels := by
      have ha : raw19282step1 = (fun i j => raw19282step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19282step1 raw19282step0; decide +kernel
      have hl : raw19282step1Labels = raw19282step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19282step0 raw19282step0Labels permutation33 permutation3
    _ = mixedMoment B node3887 node3887Labels := by rfl

def raw19283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19283Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19283step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19283step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19283 raw19283Labels = mixedMoment B node3887 node3887Labels := by
  calc
    mixedMoment B raw19283 raw19283Labels = mixedMoment B raw19283step0 raw19283step0Labels := by
      have hz : ∀ j, raw19283 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19283step0 = (fun i j => raw19283 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19283step0 raw19283; decide +kernel
      have hl : raw19283step0Labels = raw19283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19283 raw19283Labels permutation520 hz
    mixedMoment B raw19283step0 raw19283step0Labels = mixedMoment B raw19283step1 raw19283step1Labels := by
      have ha : raw19283step1 = (fun i j => raw19283step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19283step1 raw19283step0; decide +kernel
      have hl : raw19283step1Labels = raw19283step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19283step0 raw19283step0Labels permutation33 permutation3
    _ = mixedMoment B node3887 node3887Labels := by rfl

def raw19284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19284Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19284step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19284 raw19284Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw19284 raw19284Labels = mixedMoment B raw19284step0 raw19284step0Labels := by
      have ha : raw19284step0 = (fun i j => raw19284 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19284step0 raw19284; decide +kernel
      have hl : raw19284step0Labels = raw19284Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19284 raw19284Labels permutation170 permutation3
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw19285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19285Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19285step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19285 raw19285Labels = mixedMoment B node2075 node2075Labels := by
  calc
    mixedMoment B raw19285 raw19285Labels = mixedMoment B raw19285step0 raw19285step0Labels := by
      have ha : raw19285step0 = (fun i j => raw19285 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19285step0 raw19285; decide +kernel
      have hl : raw19285step0Labels = raw19285Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19285 raw19285Labels permutation157 permutation3
    _ = mixedMoment B node2075 node2075Labels := by rfl

def raw19286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19286Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19286step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19286 raw19286Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw19286 raw19286Labels = mixedMoment B raw19286step0 raw19286step0Labels := by
      have ha : raw19286step0 = (fun i j => raw19286 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19286step0 raw19286; decide +kernel
      have hl : raw19286step0Labels = raw19286Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19286 raw19286Labels permutation157 permutation3
    _ = mixedMoment B node3719 node3719Labels := by rfl

def raw19287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19287Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19287step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19287step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19287 raw19287Labels = mixedMoment B node3749 node3749Labels := by
  calc
    mixedMoment B raw19287 raw19287Labels = mixedMoment B raw19287step0 raw19287step0Labels := by
      have ha : raw19287step0 = (fun i j => raw19287 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19287step0 raw19287; decide +kernel
      have hl : raw19287step0Labels = raw19287Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19287 raw19287Labels permutation181 permutation3
    _ = mixedMoment B node3749 node3749Labels := by rfl

def raw19288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw19288Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw19288step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw19288step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19288step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19288 raw19288Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw19288 raw19288Labels = mixedMoment B raw19288step0 raw19288step0Labels := by
      have hz : ∀ j, raw19288 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19288step0 = (fun i j => raw19288 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19288step0 raw19288; decide +kernel
      have hl : raw19288step0Labels = raw19288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19288 raw19288Labels permutation520 hz
    mixedMoment B raw19288step0 raw19288step0Labels = mixedMoment B raw19288step1 raw19288step1Labels := by
      have ha : raw19288step1 = (fun i j => raw19288step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19288step1 raw19288step0; decide +kernel
      have hl : raw19288step1Labels = raw19288step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19288step0 raw19288step0Labels permutation127 permutation3
    mixedMoment B raw19288step1 raw19288step1Labels = mixedMoment B raw19288step2 raw19288step2Labels := by
      have ha : raw19288step2 = -raw19288step1 := by apply Matrix.ext; change ∀ i j, raw19288step2 i j = -(raw19288step1 i j); unfold raw19288step2 raw19288step1; decide +kernel
      have hl : raw19288step2Labels = raw19288step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw19289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw19289Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw19289step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19289step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19289 raw19289Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw19289 raw19289Labels = mixedMoment B raw19289step0 raw19289step0Labels := by
      have ha : raw19289step0 = (fun i j => raw19289 (permutation498 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19289step0 raw19289; decide +kernel
      have hl : raw19289step0Labels = raw19289Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19289 raw19289Labels permutation498 permutation3
    mixedMoment B raw19289step0 raw19289step0Labels = mixedMoment B raw19289step1 raw19289step1Labels := by
      have ha : raw19289step1 = -raw19289step0 := by apply Matrix.ext; change ∀ i j, raw19289step1 i j = -(raw19289step0 i j); unfold raw19289step1 raw19289step0; decide +kernel
      have hl : raw19289step1Labels = raw19289step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3799 node3799Labels := by rfl

def raw19290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19290Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19290step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19290 raw19290Labels = mixedMoment B node2075 node2075Labels := by
  calc
    mixedMoment B raw19290 raw19290Labels = mixedMoment B raw19290step0 raw19290step0Labels := by
      have ha : raw19290step0 = (fun i j => raw19290 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19290step0 raw19290; decide +kernel
      have hl : raw19290step0Labels = raw19290Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19290 raw19290Labels permutation156 permutation3
    _ = mixedMoment B node2075 node2075Labels := by rfl

def raw19291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19291Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19291step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19291 raw19291Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw19291 raw19291Labels = mixedMoment B raw19291step0 raw19291step0Labels := by
      have ha : raw19291step0 = (fun i j => raw19291 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19291step0 raw19291; decide +kernel
      have hl : raw19291step0Labels = raw19291Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19291 raw19291Labels permutation156 permutation3
    _ = mixedMoment B node3719 node3719Labels := by rfl

def raw19292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19292Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw19292step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19292 raw19292Labels = mixedMoment B node3749 node3749Labels := by
  calc
    mixedMoment B raw19292 raw19292Labels = mixedMoment B raw19292step0 raw19292step0Labels := by
      have ha : raw19292step0 = (fun i j => raw19292 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19292step0 raw19292; decide +kernel
      have hl : raw19292step0Labels = raw19292Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19292 raw19292Labels permutation180 permutation3
    _ = mixedMoment B node3749 node3749Labels := by rfl

def raw19293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw19293Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw19293step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw19293step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19293step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19293 raw19293Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw19293 raw19293Labels = mixedMoment B raw19293step0 raw19293step0Labels := by
      have hz : ∀ j, raw19293 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19293step0 = (fun i j => raw19293 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19293step0 raw19293; decide +kernel
      have hl : raw19293step0Labels = raw19293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19293 raw19293Labels permutation434 hz
    mixedMoment B raw19293step0 raw19293step0Labels = mixedMoment B raw19293step1 raw19293step1Labels := by
      have ha : raw19293step1 = (fun i j => raw19293step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19293step1 raw19293step0; decide +kernel
      have hl : raw19293step1Labels = raw19293step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19293step0 raw19293step0Labels permutation127 permutation3
    mixedMoment B raw19293step1 raw19293step1Labels = mixedMoment B raw19293step2 raw19293step2Labels := by
      have ha : raw19293step2 = -raw19293step1 := by apply Matrix.ext; change ∀ i j, raw19293step2 i j = -(raw19293step1 i j); unfold raw19293step2 raw19293step1; decide +kernel
      have hl : raw19293step2Labels = raw19293step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw19294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw19294Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw19294step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw19294step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw19294step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19294 raw19294Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw19294 raw19294Labels = mixedMoment B raw19294step0 raw19294step0Labels := by
      have ha : raw19294step0 = (fun i j => raw19294 (permutation562 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19294step0 raw19294; decide +kernel
      have hl : raw19294step0Labels = raw19294Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19294 raw19294Labels permutation562 permutation3
    mixedMoment B raw19294step0 raw19294step0Labels = mixedMoment B raw19294step1 raw19294step1Labels := by
      have ha : raw19294step1 = -raw19294step0 := by apply Matrix.ext; change ∀ i j, raw19294step1 i j = -(raw19294step0 i j); unfold raw19294step1 raw19294step0; decide +kernel
      have hl : raw19294step1Labels = raw19294step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3799 node3799Labels := by rfl

def raw19295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19295step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19295 raw19295Labels = mixedMoment B node2077 node2077Labels := by
  calc
    mixedMoment B raw19295 raw19295Labels = mixedMoment B raw19295step0 raw19295step0Labels := by
      have ha : raw19295step0 = (fun i j => raw19295 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19295step0 raw19295; decide +kernel
      have hl : raw19295step0Labels = raw19295Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19295 raw19295Labels permutation152 permutation3
    _ = mixedMoment B node2077 node2077Labels := by rfl

def raw19296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19296step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19296 raw19296Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw19296 raw19296Labels = mixedMoment B raw19296step0 raw19296step0Labels := by
      have ha : raw19296step0 = (fun i j => raw19296 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19296step0 raw19296; decide +kernel
      have hl : raw19296step0Labels = raw19296Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19296 raw19296Labels permutation152 permutation3
    _ = mixedMoment B node3721 node3721Labels := by rfl

def raw19297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19297step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19297 raw19297Labels = mixedMoment B node3751 node3751Labels := by
  calc
    mixedMoment B raw19297 raw19297Labels = mixedMoment B raw19297step0 raw19297step0Labels := by
      have ha : raw19297step0 = (fun i j => raw19297 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19297step0 raw19297; decide +kernel
      have hl : raw19297step0Labels = raw19297Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19297 raw19297Labels permutation176 permutation3
    _ = mixedMoment B node3751 node3751Labels := by rfl

def raw19298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw19298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19298step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19298 raw19298Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw19298 raw19298Labels = mixedMoment B raw19298step0 raw19298step0Labels := by
      have hz : ∀ j, raw19298 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw19298step0 = (fun i j => raw19298 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw19298step0 raw19298; decide +kernel
      have hl : raw19298step0Labels = raw19298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19298 raw19298Labels permutation434 hz
    mixedMoment B raw19298step0 raw19298step0Labels = mixedMoment B raw19298step1 raw19298step1Labels := by
      have ha : raw19298step1 = (fun i j => raw19298step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19298step1 raw19298step0; decide +kernel
      have hl : raw19298step1Labels = raw19298step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19298step0 raw19298step0Labels permutation32 permutation3
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw19299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw19299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19299step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw19299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19299step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical19299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19299 raw19299Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw19299 raw19299Labels = mixedMoment B raw19299step0 raw19299step0Labels := by
      have hz : ∀ j, raw19299 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw19299step0 = (fun i j => raw19299 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw19299step0 raw19299; decide +kernel
      have hl : raw19299step0Labels = raw19299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19299 raw19299Labels permutation520 hz
    mixedMoment B raw19299step0 raw19299step0Labels = mixedMoment B raw19299step1 raw19299step1Labels := by
      have ha : raw19299step1 = (fun i j => raw19299step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19299step1 raw19299step0; decide +kernel
      have hl : raw19299step1Labels = raw19299step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19299step0 raw19299step0Labels permutation32 permutation3
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw19300 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19300step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19300step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19300step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19300 raw19300Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw19300 raw19300Labels = mixedMoment B raw19300step0 raw19300step0Labels := by
      have ha : raw19300step0 = (fun i j => raw19300 (permutation426 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19300step0 raw19300; decide +kernel
      have hl : raw19300step0Labels = raw19300Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19300 raw19300Labels permutation426 permutation3
    mixedMoment B raw19300step0 raw19300step0Labels = mixedMoment B raw19300step1 raw19300step1Labels := by
      have ha : raw19300step1 = raw19300step0 := by apply Matrix.ext; unfold raw19300step1 raw19300step0; decide +kernel
      have hl : raw19300step0Labels = labelEmbedding6 ∘ raw19300step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19300step0 raw19300step0Labels raw19300step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw19301 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19301step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw19301step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19301step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19301step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19301 raw19301Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw19301 raw19301Labels = mixedMoment B raw19301step0 raw19301step0Labels := by
      have ha : raw19301step0 = (fun i j => raw19301 (permutation277 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19301step0 raw19301; decide +kernel
      have hl : raw19301step0Labels = raw19301Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19301 raw19301Labels permutation277 permutation2
    mixedMoment B raw19301step0 raw19301step0Labels = mixedMoment B raw19301step1 raw19301step1Labels := by
      have ha : raw19301step1 = -raw19301step0 := by apply Matrix.ext; change ∀ i j, raw19301step1 i j = -(raw19301step0 i j); unfold raw19301step1 raw19301step0; decide +kernel
      have hl : raw19301step1Labels = raw19301step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5472 node5472Labels := by rfl

def raw19302 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19302step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw19302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19302step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19302step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19302 raw19302Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw19302 raw19302Labels = mixedMoment B raw19302step0 raw19302step0Labels := by
      have ha : raw19302step0 = (fun i j => raw19302 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19302step0 raw19302; decide +kernel
      have hl : raw19302step0Labels = raw19302Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19302 raw19302Labels permutation271 permutation2
    mixedMoment B raw19302step0 raw19302step0Labels = mixedMoment B raw19302step1 raw19302step1Labels := by
      have ha : raw19302step1 = -raw19302step0 := by apply Matrix.ext; change ∀ i j, raw19302step1 i j = -(raw19302step0 i j); unfold raw19302step1 raw19302step0; decide +kernel
      have hl : raw19302step1Labels = raw19302step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5472 node5472Labels := by rfl

def raw19303 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw19303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw19303step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19303step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw19303step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19303 raw19303Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw19303 raw19303Labels = mixedMoment B raw19303step0 raw19303step0Labels := by
      have ha : raw19303step0 = (fun i j => raw19303 (permutation273 i) (permutation2 j)) := by apply Matrix.ext; unfold raw19303step0 raw19303; decide +kernel
      have hl : raw19303step0Labels = raw19303Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19303 raw19303Labels permutation273 permutation2
    mixedMoment B raw19303step0 raw19303step0Labels = mixedMoment B raw19303step1 raw19303step1Labels := by
      have ha : raw19303step1 = -raw19303step0 := by apply Matrix.ext; change ∀ i j, raw19303step1 i j = -(raw19303step0 i j); unfold raw19303step1 raw19303step0; decide +kernel
      have hl : raw19303step1Labels = raw19303step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5471 node5471Labels := by rfl

def raw19304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19304step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw19304step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19304step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw19304step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19304step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw19304step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19304 raw19304Labels = mixedMoment B node5150 node5150Labels := by
  calc
    mixedMoment B raw19304 raw19304Labels = mixedMoment B raw19304step0 raw19304step0Labels := by
      have ha : raw19304step0 = (fun i j => raw19304 (permutation197 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19304step0 raw19304; decide +kernel
      have hl : raw19304step0Labels = raw19304Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19304 raw19304Labels permutation197 permutation4
    mixedMoment B raw19304step0 raw19304step0Labels = mixedMoment B raw19304step1 raw19304step1Labels := by
      have ha : raw19304step1 = -raw19304step0 := by apply Matrix.ext; change ∀ i j, raw19304step1 i j = -(raw19304step0 i j); unfold raw19304step1 raw19304step0; decide +kernel
      have hl : raw19304step1Labels = raw19304step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19304step1 raw19304step1Labels = mixedMoment B raw19304step2 raw19304step2Labels := by
      have ha : raw19304step2 = raw19304step1 := by apply Matrix.ext; unfold raw19304step2 raw19304step1; decide +kernel
      have hl : raw19304step1Labels = labelEmbedding7 ∘ raw19304step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19304step1 raw19304step1Labels raw19304step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5150 node5150Labels := by rfl

def raw19305 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw19305step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19305step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw19305step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19305step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw19305step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19305 raw19305Labels = mixedMoment B node5243 node5243Labels := by
  calc
    mixedMoment B raw19305 raw19305Labels = mixedMoment B raw19305step0 raw19305step0Labels := by
      have ha : raw19305step0 = (fun i j => raw19305 (permutation314 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19305step0 raw19305; decide +kernel
      have hl : raw19305step0Labels = raw19305Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19305 raw19305Labels permutation314 permutation3
    mixedMoment B raw19305step0 raw19305step0Labels = mixedMoment B raw19305step1 raw19305step1Labels := by
      have ha : raw19305step1 = -raw19305step0 := by apply Matrix.ext; change ∀ i j, raw19305step1 i j = -(raw19305step0 i j); unfold raw19305step1 raw19305step0; decide +kernel
      have hl : raw19305step1Labels = raw19305step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19305step1 raw19305step1Labels = mixedMoment B raw19305step2 raw19305step2Labels := by
      have ha : raw19305step2 = raw19305step1 := by apply Matrix.ext; unfold raw19305step2 raw19305step1; decide +kernel
      have hl : raw19305step1Labels = labelEmbedding6 ∘ raw19305step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19305step1 raw19305step1Labels raw19305step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5243 node5243Labels := by rfl

def raw19306 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19306step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19306step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19306step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19306step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19306step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19306step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19306 raw19306Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw19306 raw19306Labels = mixedMoment B raw19306step0 raw19306step0Labels := by
      have ha : raw19306step0 = (fun i j => raw19306 (permutation323 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19306step0 raw19306; decide +kernel
      have hl : raw19306step0Labels = raw19306Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19306 raw19306Labels permutation323 permutation3
    mixedMoment B raw19306step0 raw19306step0Labels = mixedMoment B raw19306step1 raw19306step1Labels := by
      have ha : raw19306step1 = -raw19306step0 := by apply Matrix.ext; change ∀ i j, raw19306step1 i j = -(raw19306step0 i j); unfold raw19306step1 raw19306step0; decide +kernel
      have hl : raw19306step1Labels = raw19306step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19306step1 raw19306step1Labels = mixedMoment B raw19306step2 raw19306step2Labels := by
      have ha : raw19306step2 = raw19306step1 := by apply Matrix.ext; unfold raw19306step2 raw19306step1; decide +kernel
      have hl : raw19306step1Labels = labelEmbedding6 ∘ raw19306step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19306step1 raw19306step1Labels raw19306step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw19307 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19307step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw19307step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19307step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19307step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19307step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19307step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19307 raw19307Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw19307 raw19307Labels = mixedMoment B raw19307step0 raw19307step0Labels := by
      have ha : raw19307step0 = (fun i j => raw19307 (permutation308 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19307step0 raw19307; decide +kernel
      have hl : raw19307step0Labels = raw19307Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19307 raw19307Labels permutation308 permutation3
    mixedMoment B raw19307step0 raw19307step0Labels = mixedMoment B raw19307step1 raw19307step1Labels := by
      have ha : raw19307step1 = -raw19307step0 := by apply Matrix.ext; change ∀ i j, raw19307step1 i j = -(raw19307step0 i j); unfold raw19307step1 raw19307step0; decide +kernel
      have hl : raw19307step1Labels = raw19307step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19307step1 raw19307step1Labels = mixedMoment B raw19307step2 raw19307step2Labels := by
      have ha : raw19307step2 = raw19307step1 := by apply Matrix.ext; unfold raw19307step2 raw19307step1; decide +kernel
      have hl : raw19307step1Labels = labelEmbedding6 ∘ raw19307step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19307step1 raw19307step1Labels raw19307step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw19308 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw19308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw19308step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19308step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw19308step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19308step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw19308step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19308 raw19308Labels = mixedMoment B node5244 node5244Labels := by
  calc
    mixedMoment B raw19308 raw19308Labels = mixedMoment B raw19308step0 raw19308step0Labels := by
      have ha : raw19308step0 = (fun i j => raw19308 (permutation313 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19308step0 raw19308; decide +kernel
      have hl : raw19308step0Labels = raw19308Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19308 raw19308Labels permutation313 permutation3
    mixedMoment B raw19308step0 raw19308step0Labels = mixedMoment B raw19308step1 raw19308step1Labels := by
      have ha : raw19308step1 = -raw19308step0 := by apply Matrix.ext; change ∀ i j, raw19308step1 i j = -(raw19308step0 i j); unfold raw19308step1 raw19308step0; decide +kernel
      have hl : raw19308step1Labels = raw19308step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19308step1 raw19308step1Labels = mixedMoment B raw19308step2 raw19308step2Labels := by
      have ha : raw19308step2 = raw19308step1 := by apply Matrix.ext; unfold raw19308step2 raw19308step1; decide +kernel
      have hl : raw19308step1Labels = labelEmbedding6 ∘ raw19308step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19308step1 raw19308step1Labels raw19308step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5244 node5244Labels := by rfl

def raw19309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19309step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19309step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19309step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19309step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19309step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19309step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19309 raw19309Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw19309 raw19309Labels = mixedMoment B raw19309step0 raw19309step0Labels := by
      have hz : ∀ j, raw19309 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19309step0 = (fun i j => raw19309 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19309step0 raw19309; decide +kernel
      have hl : raw19309step0Labels = raw19309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19309 raw19309Labels permutation346 hz
    mixedMoment B raw19309step0 raw19309step0Labels = mixedMoment B raw19309step1 raw19309step1Labels := by
      have ha : raw19309step1 = (fun i j => raw19309step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19309step1 raw19309step0; decide +kernel
      have hl : raw19309step1Labels = raw19309step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19309step0 raw19309step0Labels permutation50 permutation4
    mixedMoment B raw19309step1 raw19309step1Labels = mixedMoment B raw19309step2 raw19309step2Labels := by
      have ha : raw19309step2 = -raw19309step1 := by apply Matrix.ext; change ∀ i j, raw19309step2 i j = -(raw19309step1 i j); unfold raw19309step2 raw19309step1; decide +kernel
      have hl : raw19309step2Labels = raw19309step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19309step2 raw19309step2Labels = mixedMoment B raw19309step3 raw19309step3Labels := by
      have ha : raw19309step3 = raw19309step2 := by apply Matrix.ext; unfold raw19309step3 raw19309step2; decide +kernel
      have hl : raw19309step2Labels = labelEmbedding7 ∘ raw19309step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19309step2 raw19309step2Labels raw19309step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw19310 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19310step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19310step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19310step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19310step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19310 raw19310Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw19310 raw19310Labels = mixedMoment B raw19310step0 raw19310step0Labels := by
      have hz : ∀ j, raw19310 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19310step0 = (fun i j => raw19310 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19310step0 raw19310; decide +kernel
      have hl : raw19310step0Labels = raw19310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19310 raw19310Labels permutation346 hz
    mixedMoment B raw19310step0 raw19310step0Labels = mixedMoment B raw19310step1 raw19310step1Labels := by
      have ha : raw19310step1 = (fun i j => raw19310step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19310step1 raw19310step0; decide +kernel
      have hl : raw19310step1Labels = raw19310step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19310step0 raw19310step0Labels permutation36 permutation6
    mixedMoment B raw19310step1 raw19310step1Labels = mixedMoment B raw19310step2 raw19310step2Labels := by
      have ha : raw19310step2 = raw19310step1 := by apply Matrix.ext; unfold raw19310step2 raw19310step1; decide +kernel
      have hl : raw19310step1Labels = labelEmbedding9 ∘ raw19310step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19310step1 raw19310step1Labels raw19310step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw19311 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw19311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw19311step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19311step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19311step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19311step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19311step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19311 raw19311Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw19311 raw19311Labels = mixedMoment B raw19311step0 raw19311step0Labels := by
      have hz : ∀ j, raw19311 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19311step0 = (fun i j => raw19311 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19311step0 raw19311; decide +kernel
      have hl : raw19311step0Labels = raw19311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19311 raw19311Labels permutation346 hz
    mixedMoment B raw19311step0 raw19311step0Labels = mixedMoment B raw19311step1 raw19311step1Labels := by
      have ha : raw19311step1 = (fun i j => raw19311step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19311step1 raw19311step0; decide +kernel
      have hl : raw19311step1Labels = raw19311step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19311step0 raw19311step0Labels permutation50 permutation4
    mixedMoment B raw19311step1 raw19311step1Labels = mixedMoment B raw19311step2 raw19311step2Labels := by
      have ha : raw19311step2 = -raw19311step1 := by apply Matrix.ext; change ∀ i j, raw19311step2 i j = -(raw19311step1 i j); unfold raw19311step2 raw19311step1; decide +kernel
      have hl : raw19311step2Labels = raw19311step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19311step2 raw19311step2Labels = mixedMoment B raw19311step3 raw19311step3Labels := by
      have ha : raw19311step3 = raw19311step2 := by apply Matrix.ext; unfold raw19311step3 raw19311step2; decide +kernel
      have hl : raw19311step2Labels = labelEmbedding7 ∘ raw19311step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19311step2 raw19311step2Labels raw19311step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw19312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19312step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19312step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19312step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19312step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19312step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19312 raw19312Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw19312 raw19312Labels = mixedMoment B raw19312step0 raw19312step0Labels := by
      have ha : raw19312step0 = (fun i j => raw19312 (permutation195 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19312step0 raw19312; decide +kernel
      have hl : raw19312step0Labels = raw19312Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19312 raw19312Labels permutation195 permutation4
    mixedMoment B raw19312step0 raw19312step0Labels = mixedMoment B raw19312step1 raw19312step1Labels := by
      have ha : raw19312step1 = -raw19312step0 := by apply Matrix.ext; change ∀ i j, raw19312step1 i j = -(raw19312step0 i j); unfold raw19312step1 raw19312step0; decide +kernel
      have hl : raw19312step1Labels = raw19312step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19312step1 raw19312step1Labels = mixedMoment B raw19312step2 raw19312step2Labels := by
      have ha : raw19312step2 = raw19312step1 := by apply Matrix.ext; unfold raw19312step2 raw19312step1; decide +kernel
      have hl : raw19312step1Labels = labelEmbedding7 ∘ raw19312step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19312step1 raw19312step1Labels raw19312step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw19313 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19313step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19313step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19313step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19313step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19313step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19313step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19313 raw19313Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw19313 raw19313Labels = mixedMoment B raw19313step0 raw19313step0Labels := by
      have ha : raw19313step0 = (fun i j => raw19313 (permutation181 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19313step0 raw19313; decide +kernel
      have hl : raw19313step0Labels = raw19313Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19313 raw19313Labels permutation181 permutation4
    mixedMoment B raw19313step0 raw19313step0Labels = mixedMoment B raw19313step1 raw19313step1Labels := by
      have ha : raw19313step1 = -raw19313step0 := by apply Matrix.ext; change ∀ i j, raw19313step1 i j = -(raw19313step0 i j); unfold raw19313step1 raw19313step0; decide +kernel
      have hl : raw19313step1Labels = raw19313step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19313step1 raw19313step1Labels = mixedMoment B raw19313step2 raw19313step2Labels := by
      have ha : raw19313step2 = raw19313step1 := by apply Matrix.ext; unfold raw19313step2 raw19313step1; decide +kernel
      have hl : raw19313step1Labels = labelEmbedding7 ∘ raw19313step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19313step1 raw19313step1Labels raw19313step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw19314 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw19314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw19314step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19314step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19314step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19314step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19314step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19314 raw19314Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw19314 raw19314Labels = mixedMoment B raw19314step0 raw19314step0Labels := by
      have ha : raw19314step0 = (fun i j => raw19314 (permutation365 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19314step0 raw19314; decide +kernel
      have hl : raw19314step0Labels = raw19314Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19314 raw19314Labels permutation365 permutation5
    mixedMoment B raw19314step0 raw19314step0Labels = mixedMoment B raw19314step1 raw19314step1Labels := by
      have ha : raw19314step1 = -raw19314step0 := by apply Matrix.ext; change ∀ i j, raw19314step1 i j = -(raw19314step0 i j); unfold raw19314step1 raw19314step0; decide +kernel
      have hl : raw19314step1Labels = raw19314step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19314step1 raw19314step1Labels = mixedMoment B raw19314step2 raw19314step2Labels := by
      have ha : raw19314step2 = raw19314step1 := by apply Matrix.ext; unfold raw19314step2 raw19314step1; decide +kernel
      have hl : raw19314step1Labels = labelEmbedding8 ∘ raw19314step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19314step1 raw19314step1Labels raw19314step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw19315 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw19315step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19315step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19315step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19315step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19315step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19315 raw19315Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw19315 raw19315Labels = mixedMoment B raw19315step0 raw19315step0Labels := by
      have ha : raw19315step0 = (fun i j => raw19315 (permutation192 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19315step0 raw19315; decide +kernel
      have hl : raw19315step0Labels = raw19315Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19315 raw19315Labels permutation192 permutation4
    mixedMoment B raw19315step0 raw19315step0Labels = mixedMoment B raw19315step1 raw19315step1Labels := by
      have ha : raw19315step1 = -raw19315step0 := by apply Matrix.ext; change ∀ i j, raw19315step1 i j = -(raw19315step0 i j); unfold raw19315step1 raw19315step0; decide +kernel
      have hl : raw19315step1Labels = raw19315step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19315step1 raw19315step1Labels = mixedMoment B raw19315step2 raw19315step2Labels := by
      have ha : raw19315step2 = raw19315step1 := by apply Matrix.ext; unfold raw19315step2 raw19315step1; decide +kernel
      have hl : raw19315step1Labels = labelEmbedding7 ∘ raw19315step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19315step1 raw19315step1Labels raw19315step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw19316 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw19316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19316step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19316step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19316step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19316step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19316 raw19316Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw19316 raw19316Labels = mixedMoment B raw19316step0 raw19316step0Labels := by
      have ha : raw19316step0 = (fun i j => raw19316 (permutation195 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19316step0 raw19316; decide +kernel
      have hl : raw19316step0Labels = raw19316Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19316 raw19316Labels permutation195 permutation4
    mixedMoment B raw19316step0 raw19316step0Labels = mixedMoment B raw19316step1 raw19316step1Labels := by
      have ha : raw19316step1 = -raw19316step0 := by apply Matrix.ext; change ∀ i j, raw19316step1 i j = -(raw19316step0 i j); unfold raw19316step1 raw19316step0; decide +kernel
      have hl : raw19316step1Labels = raw19316step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19316step1 raw19316step1Labels = mixedMoment B raw19316step2 raw19316step2Labels := by
      have ha : raw19316step2 = raw19316step1 := by apply Matrix.ext; unfold raw19316step2 raw19316step1; decide +kernel
      have hl : raw19316step1Labels = labelEmbedding7 ∘ raw19316step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19316step1 raw19316step1Labels raw19316step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

def raw19317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw19317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19317step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19317step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19317step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19317step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19317step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19317 raw19317Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw19317 raw19317Labels = mixedMoment B raw19317step0 raw19317step0Labels := by
      have ha : raw19317step0 = (fun i j => raw19317 (permutation194 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19317step0 raw19317; decide +kernel
      have hl : raw19317step0Labels = raw19317Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19317 raw19317Labels permutation194 permutation4
    mixedMoment B raw19317step0 raw19317step0Labels = mixedMoment B raw19317step1 raw19317step1Labels := by
      have ha : raw19317step1 = -raw19317step0 := by apply Matrix.ext; change ∀ i j, raw19317step1 i j = -(raw19317step0 i j); unfold raw19317step1 raw19317step0; decide +kernel
      have hl : raw19317step1Labels = raw19317step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19317step1 raw19317step1Labels = mixedMoment B raw19317step2 raw19317step2Labels := by
      have ha : raw19317step2 = raw19317step1 := by apply Matrix.ext; unfold raw19317step2 raw19317step1; decide +kernel
      have hl : raw19317step1Labels = labelEmbedding7 ∘ raw19317step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19317step1 raw19317step1Labels raw19317step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw19318 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw19318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19318step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19318step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19318step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19318step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw19318step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19318 raw19318Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw19318 raw19318Labels = mixedMoment B raw19318step0 raw19318step0Labels := by
      have ha : raw19318step0 = (fun i j => raw19318 (permutation180 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19318step0 raw19318; decide +kernel
      have hl : raw19318step0Labels = raw19318Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19318 raw19318Labels permutation180 permutation4
    mixedMoment B raw19318step0 raw19318step0Labels = mixedMoment B raw19318step1 raw19318step1Labels := by
      have ha : raw19318step1 = -raw19318step0 := by apply Matrix.ext; change ∀ i j, raw19318step1 i j = -(raw19318step0 i j); unfold raw19318step1 raw19318step0; decide +kernel
      have hl : raw19318step1Labels = raw19318step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19318step1 raw19318step1Labels = mixedMoment B raw19318step2 raw19318step2Labels := by
      have ha : raw19318step2 = raw19318step1 := by apply Matrix.ext; unfold raw19318step2 raw19318step1; decide +kernel
      have hl : raw19318step1Labels = labelEmbedding7 ∘ raw19318step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19318step1 raw19318step1Labels raw19318step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw19319 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw19319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw19319step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19319step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19319step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw19319step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw19319step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19319 raw19319Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw19319 raw19319Labels = mixedMoment B raw19319step0 raw19319step0Labels := by
      have ha : raw19319step0 = (fun i j => raw19319 (permutation363 i) (permutation5 j)) := by apply Matrix.ext; unfold raw19319step0 raw19319; decide +kernel
      have hl : raw19319step0Labels = raw19319Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19319 raw19319Labels permutation363 permutation5
    mixedMoment B raw19319step0 raw19319step0Labels = mixedMoment B raw19319step1 raw19319step1Labels := by
      have ha : raw19319step1 = -raw19319step0 := by apply Matrix.ext; change ∀ i j, raw19319step1 i j = -(raw19319step0 i j); unfold raw19319step1 raw19319step0; decide +kernel
      have hl : raw19319step1Labels = raw19319step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19319step1 raw19319step1Labels = mixedMoment B raw19319step2 raw19319step2Labels := by
      have ha : raw19319step2 = raw19319step1 := by apply Matrix.ext; unfold raw19319step2 raw19319step1; decide +kernel
      have hl : raw19319step1Labels = labelEmbedding8 ∘ raw19319step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19319step1 raw19319step1Labels raw19319step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw19320 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 0, 1]]
def raw19320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw19320step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19320step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19320step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw19320step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19320 raw19320Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw19320 raw19320Labels = mixedMoment B raw19320step0 raw19320step0Labels := by
      have ha : raw19320step0 = (fun i j => raw19320 (permutation186 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19320step0 raw19320; decide +kernel
      have hl : raw19320step0Labels = raw19320Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19320 raw19320Labels permutation186 permutation4
    mixedMoment B raw19320step0 raw19320step0Labels = mixedMoment B raw19320step1 raw19320step1Labels := by
      have ha : raw19320step1 = -raw19320step0 := by apply Matrix.ext; change ∀ i j, raw19320step1 i j = -(raw19320step0 i j); unfold raw19320step1 raw19320step0; decide +kernel
      have hl : raw19320step1Labels = raw19320step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19320step1 raw19320step1Labels = mixedMoment B raw19320step2 raw19320step2Labels := by
      have ha : raw19320step2 = raw19320step1 := by apply Matrix.ext; unfold raw19320step2 raw19320step1; decide +kernel
      have hl : raw19320step1Labels = labelEmbedding7 ∘ raw19320step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19320step1 raw19320step1Labels raw19320step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw19321 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw19321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw19321step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19321step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19321step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19321step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw19321step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19321 raw19321Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw19321 raw19321Labels = mixedMoment B raw19321step0 raw19321step0Labels := by
      have ha : raw19321step0 = (fun i j => raw19321 (permutation194 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19321step0 raw19321; decide +kernel
      have hl : raw19321step0Labels = raw19321Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19321 raw19321Labels permutation194 permutation4
    mixedMoment B raw19321step0 raw19321step0Labels = mixedMoment B raw19321step1 raw19321step1Labels := by
      have ha : raw19321step1 = -raw19321step0 := by apply Matrix.ext; change ∀ i j, raw19321step1 i j = -(raw19321step0 i j); unfold raw19321step1 raw19321step0; decide +kernel
      have hl : raw19321step1Labels = raw19321step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19321step1 raw19321step1Labels = mixedMoment B raw19321step2 raw19321step2Labels := by
      have ha : raw19321step2 = raw19321step1 := by apply Matrix.ext; unfold raw19321step2 raw19321step1; decide +kernel
      have hl : raw19321step1Labels = labelEmbedding7 ∘ raw19321step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19321step1 raw19321step1Labels raw19321step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

def raw19322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19322step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19322step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19322step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19322step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19322 raw19322Labels = mixedMoment B node5162 node5162Labels := by
  calc
    mixedMoment B raw19322 raw19322Labels = mixedMoment B raw19322step0 raw19322step0Labels := by
      have ha : raw19322step0 = (fun i j => raw19322 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19322step0 raw19322; decide +kernel
      have hl : raw19322step0Labels = raw19322Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19322 raw19322Labels permutation176 permutation4
    mixedMoment B raw19322step0 raw19322step0Labels = mixedMoment B raw19322step1 raw19322step1Labels := by
      have ha : raw19322step1 = -raw19322step0 := by apply Matrix.ext; change ∀ i j, raw19322step1 i j = -(raw19322step0 i j); unfold raw19322step1 raw19322step0; decide +kernel
      have hl : raw19322step1Labels = raw19322step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19322step1 raw19322step1Labels = mixedMoment B raw19322step2 raw19322step2Labels := by
      have ha : raw19322step2 = raw19322step1 := by apply Matrix.ext; unfold raw19322step2 raw19322step1; decide +kernel
      have hl : raw19322step1Labels = labelEmbedding7 ∘ raw19322step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19322step1 raw19322step1Labels raw19322step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5162 node5162Labels := by rfl

def raw19323 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw19323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19323step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19323step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19323step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw19323step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19323step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19323 raw19323Labels = mixedMoment B node5383 node5383Labels := by
  calc
    mixedMoment B raw19323 raw19323Labels = mixedMoment B raw19323step0 raw19323step0Labels := by
      have ha : raw19323step0 = (fun i j => raw19323 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw19323step0 raw19323; decide +kernel
      have hl : raw19323step0Labels = raw19323Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19323 raw19323Labels permutation176 permutation4
    mixedMoment B raw19323step0 raw19323step0Labels = mixedMoment B raw19323step1 raw19323step1Labels := by
      have ha : raw19323step1 = -raw19323step0 := by apply Matrix.ext; change ∀ i j, raw19323step1 i j = -(raw19323step0 i j); unfold raw19323step1 raw19323step0; decide +kernel
      have hl : raw19323step1Labels = raw19323step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19323step1 raw19323step1Labels = mixedMoment B raw19323step2 raw19323step2Labels := by
      have ha : raw19323step2 = raw19323step1 := by apply Matrix.ext; unfold raw19323step2 raw19323step1; decide +kernel
      have hl : raw19323step1Labels = labelEmbedding7 ∘ raw19323step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19323step1 raw19323step1Labels raw19323step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5383 node5383Labels := by rfl

def raw19324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19324step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19324step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw19324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw19324step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19324 raw19324Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw19324 raw19324Labels = mixedMoment B raw19324step0 raw19324step0Labels := by
      have hz : ∀ j, raw19324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19324step0 = (fun i j => raw19324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19324step0 raw19324; decide +kernel
      have hl : raw19324step0Labels = raw19324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19324 raw19324Labels permutation346 hz
    mixedMoment B raw19324step0 raw19324step0Labels = mixedMoment B raw19324step1 raw19324step1Labels := by
      have ha : raw19324step1 = (fun i j => raw19324step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw19324step1 raw19324step0; decide +kernel
      have hl : raw19324step1Labels = raw19324step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19324step0 raw19324step0Labels permutation56 permutation3
    mixedMoment B raw19324step1 raw19324step1Labels = mixedMoment B raw19324step2 raw19324step2Labels := by
      have ha : raw19324step2 = raw19324step1 := by apply Matrix.ext; unfold raw19324step2 raw19324step1; decide +kernel
      have hl : raw19324step1Labels = labelEmbedding6 ∘ raw19324step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19324step1 raw19324step1Labels raw19324step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw19325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw19325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19325step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19325step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19325step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19325step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw19325step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19325 raw19325Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw19325 raw19325Labels = mixedMoment B raw19325step0 raw19325step0Labels := by
      have ha : raw19325step0 = (fun i j => raw19325 (permutation156 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19325step0 raw19325; decide +kernel
      have hl : raw19325step0Labels = raw19325Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19325 raw19325Labels permutation156 permutation7
    mixedMoment B raw19325step0 raw19325step0Labels = mixedMoment B raw19325step1 raw19325step1Labels := by
      have ha : raw19325step1 = -raw19325step0 := by apply Matrix.ext; change ∀ i j, raw19325step1 i j = -(raw19325step0 i j); unfold raw19325step1 raw19325step0; decide +kernel
      have hl : raw19325step1Labels = raw19325step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19325step1 raw19325step1Labels = mixedMoment B raw19325step2 raw19325step2Labels := by
      have ha : raw19325step2 = raw19325step1 := by apply Matrix.ext; unfold raw19325step2 raw19325step1; decide +kernel
      have hl : raw19325step1Labels = labelEmbedding10 ∘ raw19325step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19325step1 raw19325step1Labels raw19325step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

def raw19326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw19326step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw19326step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19326step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw19326step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw19326step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19326 raw19326Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw19326 raw19326Labels = mixedMoment B raw19326step0 raw19326step0Labels := by
      have hz : ∀ j, raw19326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw19326step0 = (fun i j => raw19326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw19326step0 raw19326; decide +kernel
      have hl : raw19326step0Labels = raw19326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19326 raw19326Labels permutation346 hz
    mixedMoment B raw19326step0 raw19326step0Labels = mixedMoment B raw19326step1 raw19326step1Labels := by
      have ha : raw19326step1 = (fun i j => raw19326step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw19326step1 raw19326step0; decide +kernel
      have hl : raw19326step1Labels = raw19326step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19326step0 raw19326step0Labels permutation50 permutation6
    mixedMoment B raw19326step1 raw19326step1Labels = mixedMoment B raw19326step2 raw19326step2Labels := by
      have ha : raw19326step2 = -raw19326step1 := by apply Matrix.ext; change ∀ i j, raw19326step2 i j = -(raw19326step1 i j); unfold raw19326step2 raw19326step1; decide +kernel
      have hl : raw19326step2Labels = raw19326step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19326step2 raw19326step2Labels = mixedMoment B raw19326step3 raw19326step3Labels := by
      have ha : raw19326step3 = raw19326step2 := by apply Matrix.ext; unfold raw19326step3 raw19326step2; decide +kernel
      have hl : raw19326step2Labels = labelEmbedding9 ∘ raw19326step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19326step2 raw19326step2Labels raw19326step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw19327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw19327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19327step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19327step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw19327step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw19327step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw19327step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19327step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19327step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw19327step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw19327step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical19327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw19327 raw19327Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw19327 raw19327Labels = mixedMoment B raw19327step0 raw19327step0Labels := by
      have hz : ∀ j, raw19327 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw19327step0 = (fun i j => raw19327 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw19327step0 raw19327; decide +kernel
      have hl : raw19327step0Labels = raw19327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19327 raw19327Labels permutation590 hz
    mixedMoment B raw19327step0 raw19327step0Labels = mixedMoment B raw19327step1 raw19327step1Labels := by
      have hz : ∀ j, raw19327step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw19327step1 = (fun i j => raw19327step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw19327step1 raw19327step0; decide +kernel
      have hl : raw19327step1Labels = raw19327step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw19327step0 raw19327step0Labels permutation80 hz
    mixedMoment B raw19327step1 raw19327step1Labels = mixedMoment B raw19327step2 raw19327step2Labels := by
      have ha : raw19327step2 = (fun i j => raw19327step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw19327step2 raw19327step1; decide +kernel
      have hl : raw19327step2Labels = raw19327step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw19327step1 raw19327step1Labels permutation8 permutation7
    mixedMoment B raw19327step2 raw19327step2Labels = mixedMoment B raw19327step3 raw19327step3Labels := by
      have ha : raw19327step3 = -raw19327step2 := by apply Matrix.ext; change ∀ i j, raw19327step3 i j = -(raw19327step2 i j); unfold raw19327step3 raw19327step2; decide +kernel
      have hl : raw19327step3Labels = raw19327step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw19327step3 raw19327step3Labels = mixedMoment B raw19327step4 raw19327step4Labels := by
      have ha : raw19327step4 = raw19327step3 := by apply Matrix.ext; unfold raw19327step4 raw19327step3; decide +kernel
      have hl : raw19327step3Labels = labelEmbedding10 ∘ raw19327step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw19327step3 raw19327step3Labels raw19327step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5493 node5493Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
