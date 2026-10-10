import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw12288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12288Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12288step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12288step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12288 raw12288Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw12288 raw12288Labels = mixedMoment B raw12288step0 raw12288step0Labels := by
      have hz : ∀ j, raw12288 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12288step0 = (fun i j => raw12288 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12288step0 raw12288; decide +kernel
      have hl : raw12288step0Labels = raw12288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12288 raw12288Labels permutation265 hz
    mixedMoment B raw12288step0 raw12288step0Labels = mixedMoment B raw12288step1 raw12288step1Labels := by
      have ha : raw12288step1 = (fun i j => raw12288step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12288step1 raw12288step0; decide +kernel
      have hl : raw12288step1Labels = raw12288step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12288step0 raw12288step0Labels permutation32 permutation3
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw12289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw12289Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12289step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12289step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12289step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12289step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12289step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12289 raw12289Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw12289 raw12289Labels = mixedMoment B raw12289step0 raw12289step0Labels := by
      have hz : ∀ j, raw12289 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12289step0 = (fun i j => raw12289 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12289step0 raw12289; decide +kernel
      have hl : raw12289step0Labels = raw12289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12289 raw12289Labels permutation520 hz
    mixedMoment B raw12289step0 raw12289step0Labels = mixedMoment B raw12289step1 raw12289step1Labels := by
      have hz : ∀ j, raw12289step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12289step1 = (fun i j => raw12289step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12289step1 raw12289step0; decide +kernel
      have hl : raw12289step1Labels = raw12289step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12289step0 raw12289step0Labels permutation56 hz
    mixedMoment B raw12289step1 raw12289step1Labels = mixedMoment B raw12289step2 raw12289step2Labels := by
      have ha : raw12289step2 = (fun i j => raw12289step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12289step2 raw12289step1; decide +kernel
      have hl : raw12289step2Labels = raw12289step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12289step1 raw12289step1Labels permutation8 permutation3
    _ = mixedMoment B node3103 node3103Labels := by rfl

def raw12290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12290Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12290step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12290step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12290step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12290step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12290step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12290 raw12290Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw12290 raw12290Labels = mixedMoment B raw12290step0 raw12290step0Labels := by
      have ha : raw12290step0 = (fun i j => raw12290 (permutation202 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12290step0 raw12290; decide +kernel
      have hl : raw12290step0Labels = raw12290Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12290 raw12290Labels permutation202 permutation7
    mixedMoment B raw12290step0 raw12290step0Labels = mixedMoment B raw12290step1 raw12290step1Labels := by
      have ha : raw12290step1 = -raw12290step0 := by apply Matrix.ext; change ∀ i j, raw12290step1 i j = -(raw12290step0 i j); unfold raw12290step1 raw12290step0; decide +kernel
      have hl : raw12290step1Labels = raw12290step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12290step1 raw12290step1Labels = mixedMoment B raw12290step2 raw12290step2Labels := by
      have ha : raw12290step2 = raw12290step1 := by apply Matrix.ext; unfold raw12290step2 raw12290step1; decide +kernel
      have hl : raw12290step1Labels = labelEmbedding1 ∘ raw12290step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12290step1 raw12290step1Labels raw12290step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw12291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12291Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12291step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw12291step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw12291step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12291step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw12291step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12291 raw12291Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw12291 raw12291Labels = mixedMoment B raw12291step0 raw12291step0Labels := by
      have hz : ∀ j, raw12291 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12291step0 = (fun i j => raw12291 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12291step0 raw12291; decide +kernel
      have hl : raw12291step0Labels = raw12291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12291 raw12291Labels permutation265 hz
    mixedMoment B raw12291step0 raw12291step0Labels = mixedMoment B raw12291step1 raw12291step1Labels := by
      have ha : raw12291step1 = (fun i j => raw12291step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12291step1 raw12291step0; decide +kernel
      have hl : raw12291step1Labels = raw12291step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12291step0 raw12291step0Labels permutation40 permutation7
    mixedMoment B raw12291step1 raw12291step1Labels = mixedMoment B raw12291step2 raw12291step2Labels := by
      have ha : raw12291step2 = -raw12291step1 := by apply Matrix.ext; change ∀ i j, raw12291step2 i j = -(raw12291step1 i j); unfold raw12291step2 raw12291step1; decide +kernel
      have hl : raw12291step2Labels = raw12291step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12291step2 raw12291step2Labels = mixedMoment B raw12291step3 raw12291step3Labels := by
      have ha : raw12291step3 = raw12291step2 := by apply Matrix.ext; unfold raw12291step3 raw12291step2; decide +kernel
      have hl : raw12291step2Labels = labelEmbedding1 ∘ raw12291step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12291step2 raw12291step2Labels raw12291step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw12292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12292Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12292step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12292step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12292step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12292step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12292step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12292 raw12292Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw12292 raw12292Labels = mixedMoment B raw12292step0 raw12292step0Labels := by
      have hz : ∀ j, raw12292 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12292step0 = (fun i j => raw12292 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12292step0 raw12292; decide +kernel
      have hl : raw12292step0Labels = raw12292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12292 raw12292Labels permutation265 hz
    mixedMoment B raw12292step0 raw12292step0Labels = mixedMoment B raw12292step1 raw12292step1Labels := by
      have ha : raw12292step1 = (fun i j => raw12292step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12292step1 raw12292step0; decide +kernel
      have hl : raw12292step1Labels = raw12292step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12292step0 raw12292step0Labels permutation40 permutation7
    mixedMoment B raw12292step1 raw12292step1Labels = mixedMoment B raw12292step2 raw12292step2Labels := by
      have ha : raw12292step2 = -raw12292step1 := by apply Matrix.ext; change ∀ i j, raw12292step2 i j = -(raw12292step1 i j); unfold raw12292step2 raw12292step1; decide +kernel
      have hl : raw12292step2Labels = raw12292step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12292step2 raw12292step2Labels = mixedMoment B raw12292step3 raw12292step3Labels := by
      have ha : raw12292step3 = raw12292step2 := by apply Matrix.ext; unfold raw12292step3 raw12292step2; decide +kernel
      have hl : raw12292step2Labels = labelEmbedding1 ∘ raw12292step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12292step2 raw12292step2Labels raw12292step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw12293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12293Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12293step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12293step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12293step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12293step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12293step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12293step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12293step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12293step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12293step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12293 raw12293Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw12293 raw12293Labels = mixedMoment B raw12293step0 raw12293step0Labels := by
      have hz : ∀ j, raw12293 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12293step0 = (fun i j => raw12293 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12293step0 raw12293; decide +kernel
      have hl : raw12293step0Labels = raw12293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12293 raw12293Labels permutation520 hz
    mixedMoment B raw12293step0 raw12293step0Labels = mixedMoment B raw12293step1 raw12293step1Labels := by
      have hz : ∀ j, raw12293step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12293step1 = (fun i j => raw12293step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12293step1 raw12293step0; decide +kernel
      have hl : raw12293step1Labels = raw12293step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12293step0 raw12293step0Labels permutation56 hz
    mixedMoment B raw12293step1 raw12293step1Labels = mixedMoment B raw12293step2 raw12293step2Labels := by
      have ha : raw12293step2 = (fun i j => raw12293step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12293step2 raw12293step1; decide +kernel
      have hl : raw12293step2Labels = raw12293step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12293step1 raw12293step1Labels permutation10 permutation7
    mixedMoment B raw12293step2 raw12293step2Labels = mixedMoment B raw12293step3 raw12293step3Labels := by
      have ha : raw12293step3 = -raw12293step2 := by apply Matrix.ext; change ∀ i j, raw12293step3 i j = -(raw12293step2 i j); unfold raw12293step3 raw12293step2; decide +kernel
      have hl : raw12293step3Labels = raw12293step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12293step3 raw12293step3Labels = mixedMoment B raw12293step4 raw12293step4Labels := by
      have ha : raw12293step4 = raw12293step3 := by apply Matrix.ext; unfold raw12293step4 raw12293step3; decide +kernel
      have hl : raw12293step3Labels = labelEmbedding1 ∘ raw12293step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12293step3 raw12293step3Labels raw12293step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3888 node3888Labels := by rfl

def raw12294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12294Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12294step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw12294step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12294step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12294step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12294step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12294 raw12294Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw12294 raw12294Labels = mixedMoment B raw12294step0 raw12294step0Labels := by
      have hz : ∀ j, raw12294 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12294step0 = (fun i j => raw12294 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12294step0 raw12294; decide +kernel
      have hl : raw12294step0Labels = raw12294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12294 raw12294Labels permutation265 hz
    mixedMoment B raw12294step0 raw12294step0Labels = mixedMoment B raw12294step1 raw12294step1Labels := by
      have ha : raw12294step1 = (fun i j => raw12294step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12294step1 raw12294step0; decide +kernel
      have hl : raw12294step1Labels = raw12294step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12294step0 raw12294step0Labels permutation40 permutation7
    mixedMoment B raw12294step1 raw12294step1Labels = mixedMoment B raw12294step2 raw12294step2Labels := by
      have ha : raw12294step2 = -raw12294step1 := by apply Matrix.ext; change ∀ i j, raw12294step2 i j = -(raw12294step1 i j); unfold raw12294step2 raw12294step1; decide +kernel
      have hl : raw12294step2Labels = raw12294step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12294step2 raw12294step2Labels = mixedMoment B raw12294step3 raw12294step3Labels := by
      have ha : raw12294step3 = raw12294step2 := by apply Matrix.ext; unfold raw12294step3 raw12294step2; decide +kernel
      have hl : raw12294step2Labels = labelEmbedding1 ∘ raw12294step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12294step2 raw12294step2Labels raw12294step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3883 node3883Labels := by rfl

def raw12295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12295Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12295step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12295step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12295step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12295step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12295step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12295 raw12295Labels = mixedMoment B node3286 node3286Labels := by
  calc
    mixedMoment B raw12295 raw12295Labels = mixedMoment B raw12295step0 raw12295step0Labels := by
      have ha : raw12295step0 = (fun i j => raw12295 (permutation195 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12295step0 raw12295; decide +kernel
      have hl : raw12295step0Labels = raw12295Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12295 raw12295Labels permutation195 permutation5
    mixedMoment B raw12295step0 raw12295step0Labels = mixedMoment B raw12295step1 raw12295step1Labels := by
      have ha : raw12295step1 = -raw12295step0 := by apply Matrix.ext; change ∀ i j, raw12295step1 i j = -(raw12295step0 i j); unfold raw12295step1 raw12295step0; decide +kernel
      have hl : raw12295step1Labels = raw12295step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12295step1 raw12295step1Labels = mixedMoment B raw12295step2 raw12295step2Labels := by
      have ha : raw12295step2 = raw12295step1 := by apply Matrix.ext; unfold raw12295step2 raw12295step1; decide +kernel
      have hl : raw12295step1Labels = labelEmbedding1 ∘ raw12295step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12295step1 raw12295step1Labels raw12295step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3286 node3286Labels := by rfl

def raw12296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12296Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw12296step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw12296step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12296step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw12296step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12296 raw12296Labels = mixedMoment B node3566 node3566Labels := by
  calc
    mixedMoment B raw12296 raw12296Labels = mixedMoment B raw12296step0 raw12296step0Labels := by
      have ha : raw12296step0 = (fun i j => raw12296 (permutation202 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12296step0 raw12296; decide +kernel
      have hl : raw12296step0Labels = raw12296Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12296 raw12296Labels permutation202 permutation7
    mixedMoment B raw12296step0 raw12296step0Labels = mixedMoment B raw12296step1 raw12296step1Labels := by
      have ha : raw12296step1 = -raw12296step0 := by apply Matrix.ext; change ∀ i j, raw12296step1 i j = -(raw12296step0 i j); unfold raw12296step1 raw12296step0; decide +kernel
      have hl : raw12296step1Labels = raw12296step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12296step1 raw12296step1Labels = mixedMoment B raw12296step2 raw12296step2Labels := by
      have ha : raw12296step2 = raw12296step1 := by apply Matrix.ext; unfold raw12296step2 raw12296step1; decide +kernel
      have hl : raw12296step1Labels = labelEmbedding1 ∘ raw12296step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12296step1 raw12296step1Labels raw12296step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3566 node3566Labels := by rfl

def raw12297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12297Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12297step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12297step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12297step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12297step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12297step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12297 raw12297Labels = mixedMoment B node3525 node3525Labels := by
  calc
    mixedMoment B raw12297 raw12297Labels = mixedMoment B raw12297step0 raw12297step0Labels := by
      have ha : raw12297step0 = (fun i j => raw12297 (permutation202 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12297step0 raw12297; decide +kernel
      have hl : raw12297step0Labels = raw12297Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12297 raw12297Labels permutation202 permutation7
    mixedMoment B raw12297step0 raw12297step0Labels = mixedMoment B raw12297step1 raw12297step1Labels := by
      have ha : raw12297step1 = -raw12297step0 := by apply Matrix.ext; change ∀ i j, raw12297step1 i j = -(raw12297step0 i j); unfold raw12297step1 raw12297step0; decide +kernel
      have hl : raw12297step1Labels = raw12297step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12297step1 raw12297step1Labels = mixedMoment B raw12297step2 raw12297step2Labels := by
      have ha : raw12297step2 = raw12297step1 := by apply Matrix.ext; unfold raw12297step2 raw12297step1; decide +kernel
      have hl : raw12297step1Labels = labelEmbedding1 ∘ raw12297step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12297step1 raw12297step1Labels raw12297step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3525 node3525Labels := by rfl

def raw12298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12298Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12298step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw12298step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12298step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12298step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12298step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw12298step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12298 raw12298Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw12298 raw12298Labels = mixedMoment B raw12298step0 raw12298step0Labels := by
      have hz : ∀ j, raw12298 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12298step0 = (fun i j => raw12298 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12298step0 raw12298; decide +kernel
      have hl : raw12298step0Labels = raw12298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12298 raw12298Labels permutation520 hz
    mixedMoment B raw12298step0 raw12298step0Labels = mixedMoment B raw12298step1 raw12298step1Labels := by
      have ha : raw12298step1 = (fun i j => raw12298step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12298step1 raw12298step0; decide +kernel
      have hl : raw12298step1Labels = raw12298step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12298step0 raw12298step0Labels permutation44 permutation7
    mixedMoment B raw12298step1 raw12298step1Labels = mixedMoment B raw12298step2 raw12298step2Labels := by
      have ha : raw12298step2 = -raw12298step1 := by apply Matrix.ext; change ∀ i j, raw12298step2 i j = -(raw12298step1 i j); unfold raw12298step2 raw12298step1; decide +kernel
      have hl : raw12298step2Labels = raw12298step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12298step2 raw12298step2Labels = mixedMoment B raw12298step3 raw12298step3Labels := by
      have ha : raw12298step3 = raw12298step2 := by apply Matrix.ext; unfold raw12298step3 raw12298step2; decide +kernel
      have hl : raw12298step2Labels = labelEmbedding1 ∘ raw12298step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12298step2 raw12298step2Labels raw12298step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw12299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12299Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12299step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw12299step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12299step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12299step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12299step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12299step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12299 raw12299Labels = mixedMoment B node3567 node3567Labels := by
  calc
    mixedMoment B raw12299 raw12299Labels = mixedMoment B raw12299step0 raw12299step0Labels := by
      have ha : raw12299step0 = (fun i j => raw12299 (permutation202 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12299step0 raw12299; decide +kernel
      have hl : raw12299step0Labels = raw12299Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12299 raw12299Labels permutation202 permutation7
    mixedMoment B raw12299step0 raw12299step0Labels = mixedMoment B raw12299step1 raw12299step1Labels := by
      have ha : raw12299step1 = -raw12299step0 := by apply Matrix.ext; change ∀ i j, raw12299step1 i j = -(raw12299step0 i j); unfold raw12299step1 raw12299step0; decide +kernel
      have hl : raw12299step1Labels = raw12299step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12299step1 raw12299step1Labels = mixedMoment B raw12299step2 raw12299step2Labels := by
      have ha : raw12299step2 = raw12299step1 := by apply Matrix.ext; unfold raw12299step2 raw12299step1; decide +kernel
      have hl : raw12299step1Labels = labelEmbedding1 ∘ raw12299step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12299step1 raw12299step1Labels raw12299step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3567 node3567Labels := by rfl

def raw12300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12300Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12300step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12300step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12300step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12300step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12300step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12300step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12300 raw12300Labels = mixedMoment B node3303 node3303Labels := by
  calc
    mixedMoment B raw12300 raw12300Labels = mixedMoment B raw12300step0 raw12300step0Labels := by
      have hz : ∀ j, raw12300 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12300step0 = (fun i j => raw12300 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12300step0 raw12300; decide +kernel
      have hl : raw12300step0Labels = raw12300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12300 raw12300Labels permutation265 hz
    mixedMoment B raw12300step0 raw12300step0Labels = mixedMoment B raw12300step1 raw12300step1Labels := by
      have ha : raw12300step1 = (fun i j => raw12300step0 (permutation51 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12300step1 raw12300step0; decide +kernel
      have hl : raw12300step1Labels = raw12300step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12300step0 raw12300step0Labels permutation51 permutation5
    mixedMoment B raw12300step1 raw12300step1Labels = mixedMoment B raw12300step2 raw12300step2Labels := by
      have ha : raw12300step2 = -raw12300step1 := by apply Matrix.ext; change ∀ i j, raw12300step2 i j = -(raw12300step1 i j); unfold raw12300step2 raw12300step1; decide +kernel
      have hl : raw12300step2Labels = raw12300step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12300step2 raw12300step2Labels = mixedMoment B raw12300step3 raw12300step3Labels := by
      have ha : raw12300step3 = raw12300step2 := by apply Matrix.ext; unfold raw12300step3 raw12300step2; decide +kernel
      have hl : raw12300step2Labels = labelEmbedding1 ∘ raw12300step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12300step2 raw12300step2Labels raw12300step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3303 node3303Labels := by rfl

def raw12301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12301Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12301step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12301step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12301step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12301step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12301step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12301step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12301 raw12301Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw12301 raw12301Labels = mixedMoment B raw12301step0 raw12301step0Labels := by
      have ha : raw12301step0 = (fun i j => raw12301 (permutation202 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12301step0 raw12301; decide +kernel
      have hl : raw12301step0Labels = raw12301Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12301 raw12301Labels permutation202 permutation7
    mixedMoment B raw12301step0 raw12301step0Labels = mixedMoment B raw12301step1 raw12301step1Labels := by
      have ha : raw12301step1 = -raw12301step0 := by apply Matrix.ext; change ∀ i j, raw12301step1 i j = -(raw12301step0 i j); unfold raw12301step1 raw12301step0; decide +kernel
      have hl : raw12301step1Labels = raw12301step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12301step1 raw12301step1Labels = mixedMoment B raw12301step2 raw12301step2Labels := by
      have ha : raw12301step2 = raw12301step1 := by apply Matrix.ext; unfold raw12301step2 raw12301step1; decide +kernel
      have hl : raw12301step1Labels = labelEmbedding1 ∘ raw12301step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12301step1 raw12301step1Labels raw12301step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

def raw12302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12302Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12302step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12302step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12302step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12302step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12302step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12302step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12302 raw12302Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw12302 raw12302Labels = mixedMoment B raw12302step0 raw12302step0Labels := by
      have hz : ∀ j, raw12302 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12302step0 = (fun i j => raw12302 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12302step0 raw12302; decide +kernel
      have hl : raw12302step0Labels = raw12302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12302 raw12302Labels permutation265 hz
    mixedMoment B raw12302step0 raw12302step0Labels = mixedMoment B raw12302step1 raw12302step1Labels := by
      have ha : raw12302step1 = (fun i j => raw12302step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12302step1 raw12302step0; decide +kernel
      have hl : raw12302step1Labels = raw12302step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12302step0 raw12302step0Labels permutation40 permutation7
    mixedMoment B raw12302step1 raw12302step1Labels = mixedMoment B raw12302step2 raw12302step2Labels := by
      have ha : raw12302step2 = -raw12302step1 := by apply Matrix.ext; change ∀ i j, raw12302step2 i j = -(raw12302step1 i j); unfold raw12302step2 raw12302step1; decide +kernel
      have hl : raw12302step2Labels = raw12302step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12302step2 raw12302step2Labels = mixedMoment B raw12302step3 raw12302step3Labels := by
      have ha : raw12302step3 = raw12302step2 := by apply Matrix.ext; unfold raw12302step3 raw12302step2; decide +kernel
      have hl : raw12302step2Labels = labelEmbedding1 ∘ raw12302step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12302step2 raw12302step2Labels raw12302step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw12303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12303Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12303step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12303step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12303step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12303step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12303step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12303step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12303step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12303step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12303step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12303 raw12303Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw12303 raw12303Labels = mixedMoment B raw12303step0 raw12303step0Labels := by
      have hz : ∀ j, raw12303 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12303step0 = (fun i j => raw12303 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12303step0 raw12303; decide +kernel
      have hl : raw12303step0Labels = raw12303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12303 raw12303Labels permutation520 hz
    mixedMoment B raw12303step0 raw12303step0Labels = mixedMoment B raw12303step1 raw12303step1Labels := by
      have hz : ∀ j, raw12303step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12303step1 = (fun i j => raw12303step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12303step1 raw12303step0; decide +kernel
      have hl : raw12303step1Labels = raw12303step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12303step0 raw12303step0Labels permutation56 hz
    mixedMoment B raw12303step1 raw12303step1Labels = mixedMoment B raw12303step2 raw12303step2Labels := by
      have ha : raw12303step2 = (fun i j => raw12303step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12303step2 raw12303step1; decide +kernel
      have hl : raw12303step2Labels = raw12303step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12303step1 raw12303step1Labels permutation10 permutation7
    mixedMoment B raw12303step2 raw12303step2Labels = mixedMoment B raw12303step3 raw12303step3Labels := by
      have ha : raw12303step3 = -raw12303step2 := by apply Matrix.ext; change ∀ i j, raw12303step3 i j = -(raw12303step2 i j); unfold raw12303step3 raw12303step2; decide +kernel
      have hl : raw12303step3Labels = raw12303step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12303step3 raw12303step3Labels = mixedMoment B raw12303step4 raw12303step4Labels := by
      have ha : raw12303step4 = raw12303step3 := by apply Matrix.ext; unfold raw12303step4 raw12303step3; decide +kernel
      have hl : raw12303step3Labels = labelEmbedding1 ∘ raw12303step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12303step3 raw12303step3Labels raw12303step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3583 node3583Labels := by rfl

def raw12304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12304Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12304step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12304step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12304step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12304step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12304step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12304step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12304 raw12304Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw12304 raw12304Labels = mixedMoment B raw12304step0 raw12304step0Labels := by
      have hz : ∀ j, raw12304 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12304step0 = (fun i j => raw12304 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12304step0 raw12304; decide +kernel
      have hl : raw12304step0Labels = raw12304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12304 raw12304Labels permutation265 hz
    mixedMoment B raw12304step0 raw12304step0Labels = mixedMoment B raw12304step1 raw12304step1Labels := by
      have ha : raw12304step1 = (fun i j => raw12304step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12304step1 raw12304step0; decide +kernel
      have hl : raw12304step1Labels = raw12304step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12304step0 raw12304step0Labels permutation40 permutation7
    mixedMoment B raw12304step1 raw12304step1Labels = mixedMoment B raw12304step2 raw12304step2Labels := by
      have ha : raw12304step2 = -raw12304step1 := by apply Matrix.ext; change ∀ i j, raw12304step2 i j = -(raw12304step1 i j); unfold raw12304step2 raw12304step1; decide +kernel
      have hl : raw12304step2Labels = raw12304step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12304step2 raw12304step2Labels = mixedMoment B raw12304step3 raw12304step3Labels := by
      have ha : raw12304step3 = raw12304step2 := by apply Matrix.ext; unfold raw12304step3 raw12304step2; decide +kernel
      have hl : raw12304step2Labels = labelEmbedding1 ∘ raw12304step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12304step2 raw12304step2Labels raw12304step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw12305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12305Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12305step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw12305step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12305step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw12305step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12305 raw12305Labels = mixedMoment B node2502 node2502Labels := by
  calc
    mixedMoment B raw12305 raw12305Labels = mixedMoment B raw12305step0 raw12305step0Labels := by
      have hz : ∀ j, raw12305 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12305step0 = (fun i j => raw12305 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12305step0 raw12305; decide +kernel
      have hl : raw12305step0Labels = raw12305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12305 raw12305Labels permutation265 hz
    mixedMoment B raw12305step0 raw12305step0Labels = mixedMoment B raw12305step1 raw12305step1Labels := by
      have ha : raw12305step1 = (fun i j => raw12305step0 (permutation97 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12305step1 raw12305step0; decide +kernel
      have hl : raw12305step1Labels = raw12305step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12305step0 raw12305step0Labels permutation97 permutation5
    mixedMoment B raw12305step1 raw12305step1Labels = mixedMoment B raw12305step2 raw12305step2Labels := by
      have ha : raw12305step2 = raw12305step1 := by apply Matrix.ext; unfold raw12305step2 raw12305step1; decide +kernel
      have hl : raw12305step1Labels = labelEmbedding1 ∘ raw12305step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12305step1 raw12305step1Labels raw12305step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2502 node2502Labels := by rfl

def raw12306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12306Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12306step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12306step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12306step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw12306step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12306 raw12306Labels = mixedMoment B node2500 node2500Labels := by
  calc
    mixedMoment B raw12306 raw12306Labels = mixedMoment B raw12306step0 raw12306step0Labels := by
      have ha : raw12306step0 = (fun i j => raw12306 (permutation504 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12306step0 raw12306; decide +kernel
      have hl : raw12306step0Labels = raw12306Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12306 raw12306Labels permutation504 permutation5
    mixedMoment B raw12306step0 raw12306step0Labels = mixedMoment B raw12306step1 raw12306step1Labels := by
      have ha : raw12306step1 = raw12306step0 := by apply Matrix.ext; unfold raw12306step1 raw12306step0; decide +kernel
      have hl : raw12306step0Labels = labelEmbedding1 ∘ raw12306step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12306step0 raw12306step0Labels raw12306step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2500 node2500Labels := by rfl

def raw12307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12307Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12307step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw12307step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12307step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw12307step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12307 raw12307Labels = mixedMoment B node2506 node2506Labels := by
  calc
    mixedMoment B raw12307 raw12307Labels = mixedMoment B raw12307step0 raw12307step0Labels := by
      have hz : ∀ j, raw12307 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12307step0 = (fun i j => raw12307 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12307step0 raw12307; decide +kernel
      have hl : raw12307step0Labels = raw12307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12307 raw12307Labels permutation265 hz
    mixedMoment B raw12307step0 raw12307step0Labels = mixedMoment B raw12307step1 raw12307step1Labels := by
      have ha : raw12307step1 = (fun i j => raw12307step0 (permutation96 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12307step1 raw12307step0; decide +kernel
      have hl : raw12307step1Labels = raw12307step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12307step0 raw12307step0Labels permutation96 permutation5
    mixedMoment B raw12307step1 raw12307step1Labels = mixedMoment B raw12307step2 raw12307step2Labels := by
      have ha : raw12307step2 = raw12307step1 := by apply Matrix.ext; unfold raw12307step2 raw12307step1; decide +kernel
      have hl : raw12307step1Labels = labelEmbedding1 ∘ raw12307step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12307step1 raw12307step1Labels raw12307step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2506 node2506Labels := by rfl

def raw12308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12308Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw12308step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12308step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw12308step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12308step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw12308step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12308step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw12308step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12308 raw12308Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw12308 raw12308Labels = mixedMoment B raw12308step0 raw12308step0Labels := by
      have hz : ∀ j, raw12308 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12308step0 = (fun i j => raw12308 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12308step0 raw12308; decide +kernel
      have hl : raw12308step0Labels = raw12308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12308 raw12308Labels permutation520 hz
    mixedMoment B raw12308step0 raw12308step0Labels = mixedMoment B raw12308step1 raw12308step1Labels := by
      have hz : ∀ j, raw12308step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12308step1 = (fun i j => raw12308step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12308step1 raw12308step0; decide +kernel
      have hl : raw12308step1Labels = raw12308step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12308step0 raw12308step0Labels permutation56 hz
    mixedMoment B raw12308step1 raw12308step1Labels = mixedMoment B raw12308step2 raw12308step2Labels := by
      have ha : raw12308step2 = (fun i j => raw12308step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12308step2 raw12308step1; decide +kernel
      have hl : raw12308step2Labels = raw12308step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12308step1 raw12308step1Labels permutation25 permutation5
    mixedMoment B raw12308step2 raw12308step2Labels = mixedMoment B raw12308step3 raw12308step3Labels := by
      have ha : raw12308step3 = raw12308step2 := by apply Matrix.ext; unfold raw12308step3 raw12308step2; decide +kernel
      have hl : raw12308step2Labels = labelEmbedding1 ∘ raw12308step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12308step2 raw12308step2Labels raw12308step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2781 node2781Labels := by rfl

def raw12309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12309Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12309step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw12309step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12309step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw12309step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12309 raw12309Labels = mixedMoment B node2513 node2513Labels := by
  calc
    mixedMoment B raw12309 raw12309Labels = mixedMoment B raw12309step0 raw12309step0Labels := by
      have hz : ∀ j, raw12309 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12309step0 = (fun i j => raw12309 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12309step0 raw12309; decide +kernel
      have hl : raw12309step0Labels = raw12309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12309 raw12309Labels permutation265 hz
    mixedMoment B raw12309step0 raw12309step0Labels = mixedMoment B raw12309step1 raw12309step1Labels := by
      have ha : raw12309step1 = (fun i j => raw12309step0 (permutation94 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12309step1 raw12309step0; decide +kernel
      have hl : raw12309step1Labels = raw12309step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12309step0 raw12309step0Labels permutation94 permutation5
    mixedMoment B raw12309step1 raw12309step1Labels = mixedMoment B raw12309step2 raw12309step2Labels := by
      have ha : raw12309step2 = raw12309step1 := by apply Matrix.ext; unfold raw12309step2 raw12309step1; decide +kernel
      have hl : raw12309step1Labels = labelEmbedding1 ∘ raw12309step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12309step1 raw12309step1Labels raw12309step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2513 node2513Labels := by rfl

def raw12310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12310Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12310step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw12310step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12310step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw12310step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12310step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw12310step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12310 raw12310Labels = mixedMoment B node3287 node3287Labels := by
  calc
    mixedMoment B raw12310 raw12310Labels = mixedMoment B raw12310step0 raw12310step0Labels := by
      have hz : ∀ j, raw12310 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12310step0 = (fun i j => raw12310 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12310step0 raw12310; decide +kernel
      have hl : raw12310step0Labels = raw12310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12310 raw12310Labels permutation265 hz
    mixedMoment B raw12310step0 raw12310step0Labels = mixedMoment B raw12310step1 raw12310step1Labels := by
      have ha : raw12310step1 = (fun i j => raw12310step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12310step1 raw12310step0; decide +kernel
      have hl : raw12310step1Labels = raw12310step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12310step0 raw12310step0Labels permutation36 permutation5
    mixedMoment B raw12310step1 raw12310step1Labels = mixedMoment B raw12310step2 raw12310step2Labels := by
      have ha : raw12310step2 = -raw12310step1 := by apply Matrix.ext; change ∀ i j, raw12310step2 i j = -(raw12310step1 i j); unfold raw12310step2 raw12310step1; decide +kernel
      have hl : raw12310step2Labels = raw12310step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12310step2 raw12310step2Labels = mixedMoment B raw12310step3 raw12310step3Labels := by
      have ha : raw12310step3 = raw12310step2 := by apply Matrix.ext; unfold raw12310step3 raw12310step2; decide +kernel
      have hl : raw12310step2Labels = labelEmbedding1 ∘ raw12310step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12310step2 raw12310step2Labels raw12310step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3287 node3287Labels := by rfl

def raw12311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12311Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw12311step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12311step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12311step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12311step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12311 raw12311Labels = mixedMoment B node3560 node3560Labels := by
  calc
    mixedMoment B raw12311 raw12311Labels = mixedMoment B raw12311step0 raw12311step0Labels := by
      have ha : raw12311step0 = (fun i j => raw12311 (permutation202 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12311step0 raw12311; decide +kernel
      have hl : raw12311step0Labels = raw12311Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12311 raw12311Labels permutation202 permutation7
    mixedMoment B raw12311step0 raw12311step0Labels = mixedMoment B raw12311step1 raw12311step1Labels := by
      have ha : raw12311step1 = -raw12311step0 := by apply Matrix.ext; change ∀ i j, raw12311step1 i j = -(raw12311step0 i j); unfold raw12311step1 raw12311step0; decide +kernel
      have hl : raw12311step1Labels = raw12311step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12311step1 raw12311step1Labels = mixedMoment B raw12311step2 raw12311step2Labels := by
      have ha : raw12311step2 = raw12311step1 := by apply Matrix.ext; unfold raw12311step2 raw12311step1; decide +kernel
      have hl : raw12311step1Labels = labelEmbedding1 ∘ raw12311step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12311step1 raw12311step1Labels raw12311step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3560 node3560Labels := by rfl

def raw12312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12312Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12312step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw12312step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12312step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw12312step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12312step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw12312step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12312 raw12312Labels = mixedMoment B node3575 node3575Labels := by
  calc
    mixedMoment B raw12312 raw12312Labels = mixedMoment B raw12312step0 raw12312step0Labels := by
      have hz : ∀ j, raw12312 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12312step0 = (fun i j => raw12312 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12312step0 raw12312; decide +kernel
      have hl : raw12312step0Labels = raw12312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12312 raw12312Labels permutation265 hz
    mixedMoment B raw12312step0 raw12312step0Labels = mixedMoment B raw12312step1 raw12312step1Labels := by
      have ha : raw12312step1 = (fun i j => raw12312step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12312step1 raw12312step0; decide +kernel
      have hl : raw12312step1Labels = raw12312step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12312step0 raw12312step0Labels permutation40 permutation7
    mixedMoment B raw12312step1 raw12312step1Labels = mixedMoment B raw12312step2 raw12312step2Labels := by
      have ha : raw12312step2 = -raw12312step1 := by apply Matrix.ext; change ∀ i j, raw12312step2 i j = -(raw12312step1 i j); unfold raw12312step2 raw12312step1; decide +kernel
      have hl : raw12312step2Labels = raw12312step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12312step2 raw12312step2Labels = mixedMoment B raw12312step3 raw12312step3Labels := by
      have ha : raw12312step3 = raw12312step2 := by apply Matrix.ext; unfold raw12312step3 raw12312step2; decide +kernel
      have hl : raw12312step2Labels = labelEmbedding1 ∘ raw12312step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12312step2 raw12312step2Labels raw12312step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3575 node3575Labels := by rfl

def raw12313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12313Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12313step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw12313step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12313step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12313step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12313step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12313 raw12313Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw12313 raw12313Labels = mixedMoment B raw12313step0 raw12313step0Labels := by
      have hz : ∀ j, raw12313 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12313step0 = (fun i j => raw12313 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12313step0 raw12313; decide +kernel
      have hl : raw12313step0Labels = raw12313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12313 raw12313Labels permutation265 hz
    mixedMoment B raw12313step0 raw12313step0Labels = mixedMoment B raw12313step1 raw12313step1Labels := by
      have ha : raw12313step1 = (fun i j => raw12313step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12313step1 raw12313step0; decide +kernel
      have hl : raw12313step1Labels = raw12313step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12313step0 raw12313step0Labels permutation40 permutation7
    mixedMoment B raw12313step1 raw12313step1Labels = mixedMoment B raw12313step2 raw12313step2Labels := by
      have ha : raw12313step2 = -raw12313step1 := by apply Matrix.ext; change ∀ i j, raw12313step2 i j = -(raw12313step1 i j); unfold raw12313step2 raw12313step1; decide +kernel
      have hl : raw12313step2Labels = raw12313step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12313step2 raw12313step2Labels = mixedMoment B raw12313step3 raw12313step3Labels := by
      have ha : raw12313step3 = raw12313step2 := by apply Matrix.ext; unfold raw12313step3 raw12313step2; decide +kernel
      have hl : raw12313step2Labels = labelEmbedding1 ∘ raw12313step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12313step2 raw12313step2Labels raw12313step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw12314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw12314Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 2, -2]]
def raw12314step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw12314step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12314step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12314step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw12314step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12314 raw12314Labels = mixedMoment B node3577 node3577Labels := by
  calc
    mixedMoment B raw12314 raw12314Labels = mixedMoment B raw12314step0 raw12314step0Labels := by
      have hz : ∀ j, raw12314 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12314step0 = (fun i j => raw12314 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12314step0 raw12314; decide +kernel
      have hl : raw12314step0Labels = raw12314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12314 raw12314Labels permutation265 hz
    mixedMoment B raw12314step0 raw12314step0Labels = mixedMoment B raw12314step1 raw12314step1Labels := by
      have ha : raw12314step1 = (fun i j => raw12314step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12314step1 raw12314step0; decide +kernel
      have hl : raw12314step1Labels = raw12314step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12314step0 raw12314step0Labels permutation40 permutation7
    mixedMoment B raw12314step1 raw12314step1Labels = mixedMoment B raw12314step2 raw12314step2Labels := by
      have ha : raw12314step2 = -raw12314step1 := by apply Matrix.ext; change ∀ i j, raw12314step2 i j = -(raw12314step1 i j); unfold raw12314step2 raw12314step1; decide +kernel
      have hl : raw12314step2Labels = raw12314step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12314step2 raw12314step2Labels = mixedMoment B raw12314step3 raw12314step3Labels := by
      have ha : raw12314step3 = raw12314step2 := by apply Matrix.ext; unfold raw12314step3 raw12314step2; decide +kernel
      have hl : raw12314step2Labels = labelEmbedding1 ∘ raw12314step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12314step2 raw12314step2Labels raw12314step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3577 node3577Labels := by rfl

def raw12315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12315Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12315step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw12315step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12315step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw12315step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12315step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw12315step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12315 raw12315Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw12315 raw12315Labels = mixedMoment B raw12315step0 raw12315step0Labels := by
      have hz : ∀ j, raw12315 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12315step0 = (fun i j => raw12315 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12315step0 raw12315; decide +kernel
      have hl : raw12315step0Labels = raw12315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12315 raw12315Labels permutation265 hz
    mixedMoment B raw12315step0 raw12315step0Labels = mixedMoment B raw12315step1 raw12315step1Labels := by
      have ha : raw12315step1 = (fun i j => raw12315step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12315step1 raw12315step0; decide +kernel
      have hl : raw12315step1Labels = raw12315step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12315step0 raw12315step0Labels permutation37 permutation5
    mixedMoment B raw12315step1 raw12315step1Labels = mixedMoment B raw12315step2 raw12315step2Labels := by
      have ha : raw12315step2 = -raw12315step1 := by apply Matrix.ext; change ∀ i j, raw12315step2 i j = -(raw12315step1 i j); unfold raw12315step2 raw12315step1; decide +kernel
      have hl : raw12315step2Labels = raw12315step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12315step2 raw12315step2Labels = mixedMoment B raw12315step3 raw12315step3Labels := by
      have ha : raw12315step3 = raw12315step2 := by apply Matrix.ext; unfold raw12315step3 raw12315step2; decide +kernel
      have hl : raw12315step2Labels = labelEmbedding1 ∘ raw12315step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12315step2 raw12315step2Labels raw12315step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

def raw12316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12316Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw12316step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12316step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12316step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12316step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12316 raw12316Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw12316 raw12316Labels = mixedMoment B raw12316step0 raw12316step0Labels := by
      have ha : raw12316step0 = (fun i j => raw12316 (permutation202 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12316step0 raw12316; decide +kernel
      have hl : raw12316step0Labels = raw12316Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12316 raw12316Labels permutation202 permutation7
    mixedMoment B raw12316step0 raw12316step0Labels = mixedMoment B raw12316step1 raw12316step1Labels := by
      have ha : raw12316step1 = -raw12316step0 := by apply Matrix.ext; change ∀ i j, raw12316step1 i j = -(raw12316step0 i j); unfold raw12316step1 raw12316step0; decide +kernel
      have hl : raw12316step1Labels = raw12316step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12316step1 raw12316step1Labels = mixedMoment B raw12316step2 raw12316step2Labels := by
      have ha : raw12316step2 = raw12316step1 := by apply Matrix.ext; unfold raw12316step2 raw12316step1; decide +kernel
      have hl : raw12316step1Labels = labelEmbedding1 ∘ raw12316step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12316step1 raw12316step1Labels raw12316step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

def raw12317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12317Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12317step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw12317step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12317step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12317step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12317step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12317 raw12317Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw12317 raw12317Labels = mixedMoment B raw12317step0 raw12317step0Labels := by
      have hz : ∀ j, raw12317 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12317step0 = (fun i j => raw12317 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12317step0 raw12317; decide +kernel
      have hl : raw12317step0Labels = raw12317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12317 raw12317Labels permutation265 hz
    mixedMoment B raw12317step0 raw12317step0Labels = mixedMoment B raw12317step1 raw12317step1Labels := by
      have ha : raw12317step1 = (fun i j => raw12317step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12317step1 raw12317step0; decide +kernel
      have hl : raw12317step1Labels = raw12317step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12317step0 raw12317step0Labels permutation40 permutation7
    mixedMoment B raw12317step1 raw12317step1Labels = mixedMoment B raw12317step2 raw12317step2Labels := by
      have ha : raw12317step2 = -raw12317step1 := by apply Matrix.ext; change ∀ i j, raw12317step2 i j = -(raw12317step1 i j); unfold raw12317step2 raw12317step1; decide +kernel
      have hl : raw12317step2Labels = raw12317step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12317step2 raw12317step2Labels = mixedMoment B raw12317step3 raw12317step3Labels := by
      have ha : raw12317step3 = raw12317step2 := by apply Matrix.ext; unfold raw12317step3 raw12317step2; decide +kernel
      have hl : raw12317step2Labels = labelEmbedding1 ∘ raw12317step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12317step2 raw12317step2Labels raw12317step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3570 node3570Labels := by rfl

def raw12318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12318Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12318step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw12318step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12318step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12318step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12318step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12318 raw12318Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw12318 raw12318Labels = mixedMoment B raw12318step0 raw12318step0Labels := by
      have hz : ∀ j, raw12318 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12318step0 = (fun i j => raw12318 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12318step0 raw12318; decide +kernel
      have hl : raw12318step0Labels = raw12318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12318 raw12318Labels permutation265 hz
    mixedMoment B raw12318step0 raw12318step0Labels = mixedMoment B raw12318step1 raw12318step1Labels := by
      have ha : raw12318step1 = (fun i j => raw12318step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12318step1 raw12318step0; decide +kernel
      have hl : raw12318step1Labels = raw12318step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12318step0 raw12318step0Labels permutation40 permutation7
    mixedMoment B raw12318step1 raw12318step1Labels = mixedMoment B raw12318step2 raw12318step2Labels := by
      have ha : raw12318step2 = -raw12318step1 := by apply Matrix.ext; change ∀ i j, raw12318step2 i j = -(raw12318step1 i j); unfold raw12318step2 raw12318step1; decide +kernel
      have hl : raw12318step2Labels = raw12318step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12318step2 raw12318step2Labels = mixedMoment B raw12318step3 raw12318step3Labels := by
      have ha : raw12318step3 = raw12318step2 := by apply Matrix.ext; unfold raw12318step3 raw12318step2; decide +kernel
      have hl : raw12318step2Labels = labelEmbedding1 ∘ raw12318step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12318step2 raw12318step2Labels raw12318step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw12319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw12319Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12319step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12319step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw12319step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12319step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw12319step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12319step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12319step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12319step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw12319step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12319 raw12319Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw12319 raw12319Labels = mixedMoment B raw12319step0 raw12319step0Labels := by
      have hz : ∀ j, raw12319 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12319step0 = (fun i j => raw12319 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12319step0 raw12319; decide +kernel
      have hl : raw12319step0Labels = raw12319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12319 raw12319Labels permutation520 hz
    mixedMoment B raw12319step0 raw12319step0Labels = mixedMoment B raw12319step1 raw12319step1Labels := by
      have hz : ∀ j, raw12319step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12319step1 = (fun i j => raw12319step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12319step1 raw12319step0; decide +kernel
      have hl : raw12319step1Labels = raw12319step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12319step0 raw12319step0Labels permutation56 hz
    mixedMoment B raw12319step1 raw12319step1Labels = mixedMoment B raw12319step2 raw12319step2Labels := by
      have ha : raw12319step2 = (fun i j => raw12319step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12319step2 raw12319step1; decide +kernel
      have hl : raw12319step2Labels = raw12319step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12319step1 raw12319step1Labels permutation10 permutation7
    mixedMoment B raw12319step2 raw12319step2Labels = mixedMoment B raw12319step3 raw12319step3Labels := by
      have ha : raw12319step3 = -raw12319step2 := by apply Matrix.ext; change ∀ i j, raw12319step3 i j = -(raw12319step2 i j); unfold raw12319step3 raw12319step2; decide +kernel
      have hl : raw12319step3Labels = raw12319step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12319step3 raw12319step3Labels = mixedMoment B raw12319step4 raw12319step4Labels := by
      have ha : raw12319step4 = raw12319step3 := by apply Matrix.ext; unfold raw12319step4 raw12319step3; decide +kernel
      have hl : raw12319step3Labels = labelEmbedding1 ∘ raw12319step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12319step3 raw12319step3Labels raw12319step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3582 node3582Labels := by rfl

def raw12320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12320step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12320 raw12320Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw12320 raw12320Labels = mixedMoment B raw12320step0 raw12320step0Labels := by
      have hz : ∀ j, raw12320 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12320step0 = (fun i j => raw12320 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12320step0 raw12320; decide +kernel
      have hl : raw12320step0Labels = raw12320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12320 raw12320Labels permutation265 hz
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw12321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12321 raw12321Labels = mixedMoment B node3848 node3848Labels := by
  calc
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw12322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12322Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12322step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12322 raw12322Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw12322 raw12322Labels = mixedMoment B raw12322step0 raw12322step0Labels := by
      have hz : ∀ j, raw12322 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12322step0 = (fun i j => raw12322 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12322step0 raw12322; decide +kernel
      have hl : raw12322step0Labels = raw12322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12322 raw12322Labels permutation265 hz
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw12323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12323step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw12323step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12323 raw12323Labels = mixedMoment B node3903 node3903Labels := by
  calc
    mixedMoment B raw12323 raw12323Labels = mixedMoment B raw12323step0 raw12323step0Labels := by
      have hz : ∀ j, raw12323 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12323step0 = (fun i j => raw12323 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12323step0 raw12323; decide +kernel
      have hl : raw12323step0Labels = raw12323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12323 raw12323Labels permutation265 hz
    mixedMoment B raw12323step0 raw12323step0Labels = mixedMoment B raw12323step1 raw12323step1Labels := by
      have ha : raw12323step1 = (fun i j => raw12323step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12323step1 raw12323step0; decide +kernel
      have hl : raw12323step1Labels = raw12323step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12323step0 raw12323step0Labels permutation38 permutation2
    _ = mixedMoment B node3903 node3903Labels := by rfl

def raw12324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12324Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12324step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12324step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12324step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12324 raw12324Labels = mixedMoment B node3913 node3913Labels := by
  calc
    mixedMoment B raw12324 raw12324Labels = mixedMoment B raw12324step0 raw12324step0Labels := by
      have hz : ∀ j, raw12324 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12324step0 = (fun i j => raw12324 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12324step0 raw12324; decide +kernel
      have hl : raw12324step0Labels = raw12324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12324 raw12324Labels permutation520 hz
    mixedMoment B raw12324step0 raw12324step0Labels = mixedMoment B raw12324step1 raw12324step1Labels := by
      have hz : ∀ j, raw12324step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12324step1 = (fun i j => raw12324step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12324step1 raw12324step0; decide +kernel
      have hl : raw12324step1Labels = raw12324step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12324step0 raw12324step0Labels permutation56 hz
    _ = mixedMoment B node3913 node3913Labels := by rfl

def raw12325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12325Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw12325step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12325step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw12325step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12325 raw12325Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw12325 raw12325Labels = mixedMoment B raw12325step0 raw12325step0Labels := by
      have hz : ∀ j, raw12325 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12325step0 = (fun i j => raw12325 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12325step0 raw12325; decide +kernel
      have hl : raw12325step0Labels = raw12325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12325 raw12325Labels permutation265 hz
    mixedMoment B raw12325step0 raw12325step0Labels = mixedMoment B raw12325step1 raw12325step1Labels := by
      have ha : raw12325step1 = (fun i j => raw12325step0 (permutation135 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12325step1 raw12325step0; decide +kernel
      have hl : raw12325step1Labels = raw12325step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12325step0 raw12325step0Labels permutation135 permutation4
    mixedMoment B raw12325step1 raw12325step1Labels = mixedMoment B raw12325step2 raw12325step2Labels := by
      have ha : raw12325step2 = -raw12325step1 := by apply Matrix.ext; change ∀ i j, raw12325step2 i j = -(raw12325step1 i j); unfold raw12325step2 raw12325step1; decide +kernel
      have hl : raw12325step2Labels = raw12325step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw12326 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-1, 1], ![0, 0], ![2, -2]]
def raw12326Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12326step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-1, 1], ![2, -2]]
def raw12326step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12326step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw12326step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw12326step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw12326step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical12326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12326 raw12326Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw12326 raw12326Labels = mixedMoment B raw12326step0 raw12326step0Labels := by
      have hz : ∀ j, raw12326 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12326step0 = (fun i j => raw12326 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12326step0 raw12326; decide +kernel
      have hl : raw12326step0Labels = raw12326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12326 raw12326Labels permutation520 hz
    mixedMoment B raw12326step0 raw12326step0Labels = mixedMoment B raw12326step1 raw12326step1Labels := by
      have hz : ∀ j, raw12326step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12326step1 = (fun i j => raw12326step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12326step1 raw12326step0; decide +kernel
      have hl : raw12326step1Labels = raw12326step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12326step0 raw12326step0Labels permutation56 hz
    mixedMoment B raw12326step1 raw12326step1Labels = mixedMoment B raw12326step2 raw12326step2Labels := by
      have ha : raw12326step2 = (fun i j => raw12326step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw12326step2 raw12326step1; decide +kernel
      have hl : raw12326step2Labels = raw12326step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12326step1 raw12326step1Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw12327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12327Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12327step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12327step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12327 raw12327Labels = mixedMoment B node1259 node1259Labels := by
  calc
    mixedMoment B raw12327 raw12327Labels = mixedMoment B raw12327step0 raw12327step0Labels := by
      have ha : raw12327step0 = (fun i j => raw12327 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12327step0 raw12327; decide +kernel
      have hl : raw12327step0Labels = raw12327Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12327 raw12327Labels permutation182 permutation2
    _ = mixedMoment B node1259 node1259Labels := by rfl

def raw12328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12328Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12328step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12328 raw12328Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw12328 raw12328Labels = mixedMoment B raw12328step0 raw12328step0Labels := by
      have hz : ∀ j, raw12328 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12328step0 = (fun i j => raw12328 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12328step0 raw12328; decide +kernel
      have hl : raw12328step0Labels = raw12328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12328 raw12328Labels permutation265 hz
    mixedMoment B raw12328step0 raw12328step0Labels = mixedMoment B raw12328step1 raw12328step1Labels := by
      have ha : raw12328step1 = (fun i j => raw12328step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12328step1 raw12328step0; decide +kernel
      have hl : raw12328step1Labels = raw12328step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12328step0 raw12328step0Labels permutation40 permutation2
    _ = mixedMoment B node1291 node1291Labels := by rfl

def raw12329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12329Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12329step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw12329step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12329 raw12329Labels = mixedMoment B node1268 node1268Labels := by
  calc
    mixedMoment B raw12329 raw12329Labels = mixedMoment B raw12329step0 raw12329step0Labels := by
      have hz : ∀ j, raw12329 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12329step0 = (fun i j => raw12329 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12329step0 raw12329; decide +kernel
      have hl : raw12329step0Labels = raw12329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12329 raw12329Labels permutation265 hz
    mixedMoment B raw12329step0 raw12329step0Labels = mixedMoment B raw12329step1 raw12329step1Labels := by
      have ha : raw12329step1 = (fun i j => raw12329step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12329step1 raw12329step0; decide +kernel
      have hl : raw12329step1Labels = raw12329step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12329step0 raw12329step0Labels permutation35 permutation2
    _ = mixedMoment B node1268 node1268Labels := by rfl

def raw12330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12330 raw12330Labels = mixedMoment B node1263 node1263Labels := by
  calc
    mixedMoment B raw12330 raw12330Labels = mixedMoment B raw12330step0 raw12330step0Labels := by
      have hz : ∀ j, raw12330 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12330step0 = (fun i j => raw12330 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12330step0 raw12330; decide +kernel
      have hl : raw12330step0Labels = raw12330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12330 raw12330Labels permutation265 hz
    mixedMoment B raw12330step0 raw12330step0Labels = mixedMoment B raw12330step1 raw12330step1Labels := by
      have ha : raw12330step1 = (fun i j => raw12330step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12330step1 raw12330step0; decide +kernel
      have hl : raw12330step1Labels = raw12330step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12330step0 raw12330step0Labels permutation33 permutation2
    _ = mixedMoment B node1263 node1263Labels := by rfl

def raw12331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12331 raw12331Labels = mixedMoment B node1261 node1261Labels := by
  calc
    mixedMoment B raw12331 raw12331Labels = mixedMoment B raw12331step0 raw12331step0Labels := by
      have hz : ∀ j, raw12331 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12331step0 = (fun i j => raw12331 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12331step0 raw12331; decide +kernel
      have hl : raw12331step0Labels = raw12331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12331 raw12331Labels permutation265 hz
    _ = mixedMoment B node1261 node1261Labels := by rfl

def raw12332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12332Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12332step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12332 raw12332Labels = mixedMoment B node2587 node2587Labels := by
  calc
    mixedMoment B raw12332 raw12332Labels = mixedMoment B raw12332step0 raw12332step0Labels := by
      have ha : raw12332step0 = (fun i j => raw12332 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12332step0 raw12332; decide +kernel
      have hl : raw12332step0Labels = raw12332Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12332 raw12332Labels permutation160 permutation2
    _ = mixedMoment B node2587 node2587Labels := by rfl

def raw12333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12333Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12333step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw12333step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12333 raw12333Labels = mixedMoment B node2571 node2571Labels := by
  calc
    mixedMoment B raw12333 raw12333Labels = mixedMoment B raw12333step0 raw12333step0Labels := by
      have ha : raw12333step0 = (fun i j => raw12333 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12333step0 raw12333; decide +kernel
      have hl : raw12333step0Labels = raw12333Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12333 raw12333Labels permutation155 permutation2
    _ = mixedMoment B node2571 node2571Labels := by rfl

def raw12334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12334Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12334 raw12334Labels = mixedMoment B node2568 node2568Labels := by
  calc
    mixedMoment B raw12334 raw12334Labels = mixedMoment B raw12334step0 raw12334step0Labels := by
      have ha : raw12334step0 = (fun i j => raw12334 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12334step0 raw12334; decide +kernel
      have hl : raw12334step0Labels = raw12334Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12334 raw12334Labels permutation153 permutation2
    _ = mixedMoment B node2568 node2568Labels := by rfl

def raw12335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12335 raw12335Labels = mixedMoment B node2566 node2566Labels := by
  calc
    _ = mixedMoment B node2566 node2566Labels := by rfl

def raw12336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12336step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12336 raw12336Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw12336 raw12336Labels = mixedMoment B raw12336step0 raw12336step0Labels := by
      have hz : ∀ j, raw12336 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12336step0 = (fun i j => raw12336 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12336step0 raw12336; decide +kernel
      have hl : raw12336step0Labels = raw12336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12336 raw12336Labels permutation265 hz
    mixedMoment B raw12336step0 raw12336step0Labels = mixedMoment B raw12336step1 raw12336step1Labels := by
      have ha : raw12336step1 = (fun i j => raw12336step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12336step1 raw12336step0; decide +kernel
      have hl : raw12336step1Labels = raw12336step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12336step0 raw12336step0Labels permutation40 permutation2
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw12337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2]]
def raw12337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw12337step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12337step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12337step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12337 raw12337Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw12337 raw12337Labels = mixedMoment B raw12337step0 raw12337step0Labels := by
      have hz : ∀ j, raw12337 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw12337step0 = (fun i j => raw12337 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw12337step0 raw12337; decide +kernel
      have hl : raw12337step0Labels = raw12337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12337 raw12337Labels permutation520 hz
    mixedMoment B raw12337step0 raw12337step0Labels = mixedMoment B raw12337step1 raw12337step1Labels := by
      have hz : ∀ j, raw12337step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw12337step1 = (fun i j => raw12337step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw12337step1 raw12337step0; decide +kernel
      have hl : raw12337step1Labels = raw12337step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12337step0 raw12337step0Labels permutation56 hz
    mixedMoment B raw12337step1 raw12337step1Labels = mixedMoment B raw12337step2 raw12337step2Labels := by
      have ha : raw12337step2 = (fun i j => raw12337step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12337step2 raw12337step1; decide +kernel
      have hl : raw12337step2Labels = raw12337step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12337step1 raw12337step1Labels permutation10 permutation2
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw12338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 2, -2]]
def raw12338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12338 raw12338Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw12338 raw12338Labels = mixedMoment B raw12338step0 raw12338step0Labels := by
      have hz : ∀ j, raw12338 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12338step0 = (fun i j => raw12338 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12338step0 raw12338; decide +kernel
      have hl : raw12338step0Labels = raw12338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12338 raw12338Labels permutation265 hz
    mixedMoment B raw12338step0 raw12338step0Labels = mixedMoment B raw12338step1 raw12338step1Labels := by
      have ha : raw12338step1 = (fun i j => raw12338step0 (permutation53 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12338step1 raw12338step0; decide +kernel
      have hl : raw12338step1Labels = raw12338step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12338step0 raw12338step0Labels permutation53 permutation2
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw12339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12339Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12339step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12339 raw12339Labels = mixedMoment B node2630 node2630Labels := by
  calc
    mixedMoment B raw12339 raw12339Labels = mixedMoment B raw12339step0 raw12339step0Labels := by
      have ha : raw12339step0 = (fun i j => raw12339 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12339step0 raw12339; decide +kernel
      have hl : raw12339step0Labels = raw12339Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12339 raw12339Labels permutation182 permutation2
    _ = mixedMoment B node2630 node2630Labels := by rfl

def raw12340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12340Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw12340step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12340 raw12340Labels = mixedMoment B node2639 node2639Labels := by
  calc
    mixedMoment B raw12340 raw12340Labels = mixedMoment B raw12340step0 raw12340step0Labels := by
      have hz : ∀ j, raw12340 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12340step0 = (fun i j => raw12340 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12340step0 raw12340; decide +kernel
      have hl : raw12340step0Labels = raw12340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12340 raw12340Labels permutation265 hz
    mixedMoment B raw12340step0 raw12340step0Labels = mixedMoment B raw12340step1 raw12340step1Labels := by
      have ha : raw12340step1 = (fun i j => raw12340step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12340step1 raw12340step0; decide +kernel
      have hl : raw12340step1Labels = raw12340step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12340step0 raw12340step0Labels permutation35 permutation2
    _ = mixedMoment B node2639 node2639Labels := by rfl

def raw12341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw12341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12341 raw12341Labels = mixedMoment B node2634 node2634Labels := by
  calc
    mixedMoment B raw12341 raw12341Labels = mixedMoment B raw12341step0 raw12341step0Labels := by
      have hz : ∀ j, raw12341 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12341step0 = (fun i j => raw12341 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12341step0 raw12341; decide +kernel
      have hl : raw12341step0Labels = raw12341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12341 raw12341Labels permutation265 hz
    mixedMoment B raw12341step0 raw12341step0Labels = mixedMoment B raw12341step1 raw12341step1Labels := by
      have ha : raw12341step1 = (fun i j => raw12341step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12341step1 raw12341step0; decide +kernel
      have hl : raw12341step1Labels = raw12341step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12341step0 raw12341step0Labels permutation33 permutation2
    _ = mixedMoment B node2634 node2634Labels := by rfl

def raw12342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12342Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw12342step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12342 raw12342Labels = mixedMoment B node2632 node2632Labels := by
  calc
    mixedMoment B raw12342 raw12342Labels = mixedMoment B raw12342step0 raw12342step0Labels := by
      have hz : ∀ j, raw12342 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12342step0 = (fun i j => raw12342 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12342step0 raw12342; decide +kernel
      have hl : raw12342step0Labels = raw12342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12342 raw12342Labels permutation265 hz
    _ = mixedMoment B node2632 node2632Labels := by rfl

def raw12343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12343step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12343step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12343step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12343 raw12343Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw12343 raw12343Labels = mixedMoment B raw12343step0 raw12343step0Labels := by
      have ha : raw12343step0 = (fun i j => raw12343 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12343step0 raw12343; decide +kernel
      have hl : raw12343step0Labels = raw12343Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12343 raw12343Labels permutation152 permutation3
    mixedMoment B raw12343step0 raw12343step0Labels = mixedMoment B raw12343step1 raw12343step1Labels := by
      have ha : raw12343step1 = raw12343step0 := by apply Matrix.ext; unfold raw12343step1 raw12343step0; decide +kernel
      have hl : raw12343step0Labels = labelEmbedding6 ∘ raw12343step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12343step0 raw12343step0Labels raw12343step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5480 node5480Labels := by rfl

def raw12344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12344step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12344step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12344 raw12344Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw12344 raw12344Labels = mixedMoment B raw12344step0 raw12344step0Labels := by
      have hz : ∀ j, raw12344 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12344step0 = (fun i j => raw12344 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12344step0 raw12344; decide +kernel
      have hl : raw12344step0Labels = raw12344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12344 raw12344Labels permutation265 hz
    mixedMoment B raw12344step0 raw12344step0Labels = mixedMoment B raw12344step1 raw12344step1Labels := by
      have ha : raw12344step1 = (fun i j => raw12344step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw12344step1 raw12344step0; decide +kernel
      have hl : raw12344step1Labels = raw12344step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12344step0 raw12344step0Labels permutation37 permutation2
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw12345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12345step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12345step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12345step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12345 raw12345Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw12345 raw12345Labels = mixedMoment B raw12345step0 raw12345step0Labels := by
      have hz : ∀ j, raw12345 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12345step0 = (fun i j => raw12345 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12345step0 raw12345; decide +kernel
      have hl : raw12345step0Labels = raw12345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12345 raw12345Labels permutation265 hz
    mixedMoment B raw12345step0 raw12345step0Labels = mixedMoment B raw12345step1 raw12345step1Labels := by
      have ha : raw12345step1 = (fun i j => raw12345step0 (permutation92 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12345step1 raw12345step0; decide +kernel
      have hl : raw12345step1Labels = raw12345step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12345step0 raw12345step0Labels permutation92 permutation6
    mixedMoment B raw12345step1 raw12345step1Labels = mixedMoment B raw12345step2 raw12345step2Labels := by
      have ha : raw12345step2 = raw12345step1 := by apply Matrix.ext; unfold raw12345step2 raw12345step1; decide +kernel
      have hl : raw12345step1Labels = labelEmbedding9 ∘ raw12345step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12345step1 raw12345step1Labels raw12345step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw12346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12346step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12346step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12346step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12346step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12346 raw12346Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw12346 raw12346Labels = mixedMoment B raw12346step0 raw12346step0Labels := by
      have hz : ∀ j, raw12346 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12346step0 = (fun i j => raw12346 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12346step0 raw12346; decide +kernel
      have hl : raw12346step0Labels = raw12346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12346 raw12346Labels permutation265 hz
    mixedMoment B raw12346step0 raw12346step0Labels = mixedMoment B raw12346step1 raw12346step1Labels := by
      have ha : raw12346step1 = (fun i j => raw12346step0 (permutation135 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12346step1 raw12346step0; decide +kernel
      have hl : raw12346step1Labels = raw12346step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12346step0 raw12346step0Labels permutation135 permutation4
    mixedMoment B raw12346step1 raw12346step1Labels = mixedMoment B raw12346step2 raw12346step2Labels := by
      have ha : raw12346step2 = raw12346step1 := by apply Matrix.ext; unfold raw12346step2 raw12346step1; decide +kernel
      have hl : raw12346step1Labels = labelEmbedding7 ∘ raw12346step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12346step1 raw12346step1Labels raw12346step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw12347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12347step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12347step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12347step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12347step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12347 raw12347Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw12347 raw12347Labels = mixedMoment B raw12347step0 raw12347step0Labels := by
      have hz : ∀ j, raw12347 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12347step0 = (fun i j => raw12347 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12347step0 raw12347; decide +kernel
      have hl : raw12347step0Labels = raw12347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12347 raw12347Labels permutation265 hz
    mixedMoment B raw12347step0 raw12347step0Labels = mixedMoment B raw12347step1 raw12347step1Labels := by
      have ha : raw12347step1 = (fun i j => raw12347step0 (permutation95 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12347step1 raw12347step0; decide +kernel
      have hl : raw12347step1Labels = raw12347step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12347step0 raw12347step0Labels permutation95 permutation7
    mixedMoment B raw12347step1 raw12347step1Labels = mixedMoment B raw12347step2 raw12347step2Labels := by
      have ha : raw12347step2 = raw12347step1 := by apply Matrix.ext; unfold raw12347step2 raw12347step1; decide +kernel
      have hl : raw12347step1Labels = labelEmbedding10 ∘ raw12347step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12347step1 raw12347step1Labels raw12347step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw12348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12348step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12348step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12348step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12348 raw12348Labels = mixedMoment B node4449 node4449Labels := by
  calc
    mixedMoment B raw12348 raw12348Labels = mixedMoment B raw12348step0 raw12348step0Labels := by
      have ha : raw12348step0 = (fun i j => raw12348 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12348step0 raw12348; decide +kernel
      have hl : raw12348step0Labels = raw12348Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12348 raw12348Labels permutation184 permutation3
    mixedMoment B raw12348step0 raw12348step0Labels = mixedMoment B raw12348step1 raw12348step1Labels := by
      have ha : raw12348step1 = raw12348step0 := by apply Matrix.ext; unfold raw12348step1 raw12348step0; decide +kernel
      have hl : raw12348step0Labels = labelEmbedding6 ∘ raw12348step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12348step0 raw12348step0Labels raw12348step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4449 node4449Labels := by rfl

def raw12349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12349step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12349step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12349step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12349step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12349 raw12349Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw12349 raw12349Labels = mixedMoment B raw12349step0 raw12349step0Labels := by
      have ha : raw12349step0 = (fun i j => raw12349 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12349step0 raw12349; decide +kernel
      have hl : raw12349step0Labels = raw12349Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12349 raw12349Labels permutation184 permutation3
    mixedMoment B raw12349step0 raw12349step0Labels = mixedMoment B raw12349step1 raw12349step1Labels := by
      have ha : raw12349step1 = raw12349step0 := by apply Matrix.ext; unfold raw12349step1 raw12349step0; decide +kernel
      have hl : raw12349step0Labels = labelEmbedding6 ∘ raw12349step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12349step0 raw12349step0Labels raw12349step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw12350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12350step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12350step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12350step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12350step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12350 raw12350Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw12350 raw12350Labels = mixedMoment B raw12350step0 raw12350step0Labels := by
      have ha : raw12350step0 = (fun i j => raw12350 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12350step0 raw12350; decide +kernel
      have hl : raw12350step0Labels = raw12350Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12350 raw12350Labels permutation208 permutation3
    mixedMoment B raw12350step0 raw12350step0Labels = mixedMoment B raw12350step1 raw12350step1Labels := by
      have ha : raw12350step1 = raw12350step0 := by apply Matrix.ext; unfold raw12350step1 raw12350step0; decide +kernel
      have hl : raw12350step0Labels = labelEmbedding6 ∘ raw12350step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12350step0 raw12350step0Labels raw12350step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw12351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12351step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12351step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12351step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12351 raw12351Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw12351 raw12351Labels = mixedMoment B raw12351step0 raw12351step0Labels := by
      have ha : raw12351step0 = (fun i j => raw12351 (permutation232 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12351step0 raw12351; decide +kernel
      have hl : raw12351step0Labels = raw12351Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12351 raw12351Labels permutation232 permutation3
    mixedMoment B raw12351step0 raw12351step0Labels = mixedMoment B raw12351step1 raw12351step1Labels := by
      have ha : raw12351step1 = raw12351step0 := by apply Matrix.ext; unfold raw12351step1 raw12351step0; decide +kernel
      have hl : raw12351step0Labels = labelEmbedding6 ∘ raw12351step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12351step0 raw12351step0Labels raw12351step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

def raw12352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12352step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12352step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12352step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12352 raw12352Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw12352 raw12352Labels = mixedMoment B raw12352step0 raw12352step0Labels := by
      have ha : raw12352step0 = (fun i j => raw12352 (permutation197 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12352step0 raw12352; decide +kernel
      have hl : raw12352step0Labels = raw12352Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12352 raw12352Labels permutation197 permutation3
    mixedMoment B raw12352step0 raw12352step0Labels = mixedMoment B raw12352step1 raw12352step1Labels := by
      have ha : raw12352step1 = raw12352step0 := by apply Matrix.ext; unfold raw12352step1 raw12352step0; decide +kernel
      have hl : raw12352step0Labels = labelEmbedding6 ∘ raw12352step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12352step0 raw12352step0Labels raw12352step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw12353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12353step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12353step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12353step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12353 raw12353Labels = mixedMoment B node4487 node4487Labels := by
  calc
    mixedMoment B raw12353 raw12353Labels = mixedMoment B raw12353step0 raw12353step0Labels := by
      have hz : ∀ j, raw12353 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12353step0 = (fun i j => raw12353 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12353step0 raw12353; decide +kernel
      have hl : raw12353step0Labels = raw12353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12353 raw12353Labels permutation265 hz
    mixedMoment B raw12353step0 raw12353step0Labels = mixedMoment B raw12353step1 raw12353step1Labels := by
      have ha : raw12353step1 = (fun i j => raw12353step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12353step1 raw12353step0; decide +kernel
      have hl : raw12353step1Labels = raw12353step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12353step0 raw12353step0Labels permutation40 permutation3
    mixedMoment B raw12353step1 raw12353step1Labels = mixedMoment B raw12353step2 raw12353step2Labels := by
      have ha : raw12353step2 = raw12353step1 := by apply Matrix.ext; unfold raw12353step2 raw12353step1; decide +kernel
      have hl : raw12353step1Labels = labelEmbedding6 ∘ raw12353step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12353step1 raw12353step1Labels raw12353step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4487 node4487Labels := by rfl

def raw12354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12354step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12354step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12354 raw12354Labels = mixedMoment B node5092 node5092Labels := by
  calc
    mixedMoment B raw12354 raw12354Labels = mixedMoment B raw12354step0 raw12354step0Labels := by
      have ha : raw12354step0 = (fun i j => raw12354 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12354step0 raw12354; decide +kernel
      have hl : raw12354step0Labels = raw12354Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12354 raw12354Labels permutation160 permutation3
    mixedMoment B raw12354step0 raw12354step0Labels = mixedMoment B raw12354step1 raw12354step1Labels := by
      have ha : raw12354step1 = raw12354step0 := by apply Matrix.ext; unfold raw12354step1 raw12354step0; decide +kernel
      have hl : raw12354step0Labels = labelEmbedding6 ∘ raw12354step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12354step0 raw12354step0Labels raw12354step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5092 node5092Labels := by rfl

def raw12355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12355step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12355step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12355step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12355 raw12355Labels = mixedMoment B node5236 node5236Labels := by
  calc
    mixedMoment B raw12355 raw12355Labels = mixedMoment B raw12355step0 raw12355step0Labels := by
      have hz : ∀ j, raw12355 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12355step0 = (fun i j => raw12355 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12355step0 raw12355; decide +kernel
      have hl : raw12355step0Labels = raw12355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12355 raw12355Labels permutation265 hz
    mixedMoment B raw12355step0 raw12355step0Labels = mixedMoment B raw12355step1 raw12355step1Labels := by
      have ha : raw12355step1 = (fun i j => raw12355step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12355step1 raw12355step0; decide +kernel
      have hl : raw12355step1Labels = raw12355step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12355step0 raw12355step0Labels permutation40 permutation3
    mixedMoment B raw12355step1 raw12355step1Labels = mixedMoment B raw12355step2 raw12355step2Labels := by
      have ha : raw12355step2 = raw12355step1 := by apply Matrix.ext; unfold raw12355step2 raw12355step1; decide +kernel
      have hl : raw12355step1Labels = labelEmbedding6 ∘ raw12355step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12355step1 raw12355step1Labels raw12355step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5236 node5236Labels := by rfl

def raw12356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12356step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw12356step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12356step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw12356step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12356 raw12356Labels = mixedMoment B node5269 node5269Labels := by
  calc
    mixedMoment B raw12356 raw12356Labels = mixedMoment B raw12356step0 raw12356step0Labels := by
      have hz : ∀ j, raw12356 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12356step0 = (fun i j => raw12356 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12356step0 raw12356; decide +kernel
      have hl : raw12356step0Labels = raw12356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12356 raw12356Labels permutation265 hz
    mixedMoment B raw12356step0 raw12356step0Labels = mixedMoment B raw12356step1 raw12356step1Labels := by
      have ha : raw12356step1 = (fun i j => raw12356step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12356step1 raw12356step0; decide +kernel
      have hl : raw12356step1Labels = raw12356step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12356step0 raw12356step0Labels permutation46 permutation3
    mixedMoment B raw12356step1 raw12356step1Labels = mixedMoment B raw12356step2 raw12356step2Labels := by
      have ha : raw12356step2 = raw12356step1 := by apply Matrix.ext; unfold raw12356step2 raw12356step1; decide +kernel
      have hl : raw12356step1Labels = labelEmbedding6 ∘ raw12356step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12356step1 raw12356step1Labels raw12356step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5269 node5269Labels := by rfl

def raw12357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12357step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12357step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12357step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12357step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12357 raw12357Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw12357 raw12357Labels = mixedMoment B raw12357step0 raw12357step0Labels := by
      have hz : ∀ j, raw12357 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12357step0 = (fun i j => raw12357 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12357step0 raw12357; decide +kernel
      have hl : raw12357step0Labels = raw12357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12357 raw12357Labels permutation265 hz
    mixedMoment B raw12357step0 raw12357step0Labels = mixedMoment B raw12357step1 raw12357step1Labels := by
      have ha : raw12357step1 = (fun i j => raw12357step0 (permutation53 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12357step1 raw12357step0; decide +kernel
      have hl : raw12357step1Labels = raw12357step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12357step0 raw12357step0Labels permutation53 permutation3
    mixedMoment B raw12357step1 raw12357step1Labels = mixedMoment B raw12357step2 raw12357step2Labels := by
      have ha : raw12357step2 = raw12357step1 := by apply Matrix.ext; unfold raw12357step2 raw12357step1; decide +kernel
      have hl : raw12357step1Labels = labelEmbedding6 ∘ raw12357step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12357step1 raw12357step1Labels raw12357step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw12358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12358step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12358step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12358step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12358 raw12358Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw12358 raw12358Labels = mixedMoment B raw12358step0 raw12358step0Labels := by
      have hz : ∀ j, raw12358 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12358step0 = (fun i j => raw12358 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12358step0 raw12358; decide +kernel
      have hl : raw12358step0Labels = raw12358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12358 raw12358Labels permutation265 hz
    mixedMoment B raw12358step0 raw12358step0Labels = mixedMoment B raw12358step1 raw12358step1Labels := by
      have ha : raw12358step1 = (fun i j => raw12358step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12358step1 raw12358step0; decide +kernel
      have hl : raw12358step1Labels = raw12358step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12358step0 raw12358step0Labels permutation35 permutation3
    mixedMoment B raw12358step1 raw12358step1Labels = mixedMoment B raw12358step2 raw12358step2Labels := by
      have ha : raw12358step2 = raw12358step1 := by apply Matrix.ext; unfold raw12358step2 raw12358step1; decide +kernel
      have hl : raw12358step1Labels = labelEmbedding6 ∘ raw12358step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12358step1 raw12358step1Labels raw12358step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw12359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12359step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12359step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12359step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12359 raw12359Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw12359 raw12359Labels = mixedMoment B raw12359step0 raw12359step0Labels := by
      have ha : raw12359step0 = (fun i j => raw12359 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12359step0 raw12359; decide +kernel
      have hl : raw12359step0Labels = raw12359Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12359 raw12359Labels permutation155 permutation3
    mixedMoment B raw12359step0 raw12359step0Labels = mixedMoment B raw12359step1 raw12359step1Labels := by
      have ha : raw12359step1 = raw12359step0 := by apply Matrix.ext; unfold raw12359step1 raw12359step0; decide +kernel
      have hl : raw12359step0Labels = labelEmbedding6 ∘ raw12359step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12359step0 raw12359step0Labels raw12359step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5074 node5074Labels := by rfl

def raw12360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12360step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12360step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12360step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12360step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12360 raw12360Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw12360 raw12360Labels = mixedMoment B raw12360step0 raw12360step0Labels := by
      have hz : ∀ j, raw12360 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12360step0 = (fun i j => raw12360 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12360step0 raw12360; decide +kernel
      have hl : raw12360step0Labels = raw12360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12360 raw12360Labels permutation265 hz
    mixedMoment B raw12360step0 raw12360step0Labels = mixedMoment B raw12360step1 raw12360step1Labels := by
      have ha : raw12360step1 = (fun i j => raw12360step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12360step1 raw12360step0; decide +kernel
      have hl : raw12360step1Labels = raw12360step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12360step0 raw12360step0Labels permutation35 permutation3
    mixedMoment B raw12360step1 raw12360step1Labels = mixedMoment B raw12360step2 raw12360step2Labels := by
      have ha : raw12360step2 = raw12360step1 := by apply Matrix.ext; unfold raw12360step2 raw12360step1; decide +kernel
      have hl : raw12360step1Labels = labelEmbedding6 ∘ raw12360step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12360step1 raw12360step1Labels raw12360step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw12361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12361step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12361step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12361step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12361step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12361 raw12361Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw12361 raw12361Labels = mixedMoment B raw12361step0 raw12361step0Labels := by
      have hz : ∀ j, raw12361 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12361step0 = (fun i j => raw12361 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12361step0 raw12361; decide +kernel
      have hl : raw12361step0Labels = raw12361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12361 raw12361Labels permutation265 hz
    mixedMoment B raw12361step0 raw12361step0Labels = mixedMoment B raw12361step1 raw12361step1Labels := by
      have ha : raw12361step1 = (fun i j => raw12361step0 (permutation45 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12361step1 raw12361step0; decide +kernel
      have hl : raw12361step1Labels = raw12361step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12361step0 raw12361step0Labels permutation45 permutation3
    mixedMoment B raw12361step1 raw12361step1Labels = mixedMoment B raw12361step2 raw12361step2Labels := by
      have ha : raw12361step2 = raw12361step1 := by apply Matrix.ext; unfold raw12361step2 raw12361step1; decide +kernel
      have hl : raw12361step1Labels = labelEmbedding6 ∘ raw12361step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12361step1 raw12361step1Labels raw12361step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw12362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12362step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12362step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12362step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12362 raw12362Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw12362 raw12362Labels = mixedMoment B raw12362step0 raw12362step0Labels := by
      have hz : ∀ j, raw12362 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12362step0 = (fun i j => raw12362 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12362step0 raw12362; decide +kernel
      have hl : raw12362step0Labels = raw12362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12362 raw12362Labels permutation265 hz
    mixedMoment B raw12362step0 raw12362step0Labels = mixedMoment B raw12362step1 raw12362step1Labels := by
      have ha : raw12362step1 = (fun i j => raw12362step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12362step1 raw12362step0; decide +kernel
      have hl : raw12362step1Labels = raw12362step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12362step0 raw12362step0Labels permutation37 permutation3
    mixedMoment B raw12362step1 raw12362step1Labels = mixedMoment B raw12362step2 raw12362step2Labels := by
      have ha : raw12362step2 = raw12362step1 := by apply Matrix.ext; unfold raw12362step2 raw12362step1; decide +kernel
      have hl : raw12362step1Labels = labelEmbedding6 ∘ raw12362step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12362step1 raw12362step1Labels raw12362step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw12363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12363step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12363step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12363step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12363 raw12363Labels = mixedMoment B node4453 node4453Labels := by
  calc
    mixedMoment B raw12363 raw12363Labels = mixedMoment B raw12363step0 raw12363step0Labels := by
      have hz : ∀ j, raw12363 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12363step0 = (fun i j => raw12363 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12363step0 raw12363; decide +kernel
      have hl : raw12363step0Labels = raw12363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12363 raw12363Labels permutation265 hz
    mixedMoment B raw12363step0 raw12363step0Labels = mixedMoment B raw12363step1 raw12363step1Labels := by
      have ha : raw12363step1 = (fun i j => raw12363step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12363step1 raw12363step0; decide +kernel
      have hl : raw12363step1Labels = raw12363step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12363step0 raw12363step0Labels permutation33 permutation3
    mixedMoment B raw12363step1 raw12363step1Labels = mixedMoment B raw12363step2 raw12363step2Labels := by
      have ha : raw12363step2 = raw12363step1 := by apply Matrix.ext; unfold raw12363step2 raw12363step1; decide +kernel
      have hl : raw12363step1Labels = labelEmbedding6 ∘ raw12363step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12363step1 raw12363step1Labels raw12363step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4453 node4453Labels := by rfl

def raw12364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12364step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12364step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12364step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12364step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12364 raw12364Labels = mixedMoment B node5071 node5071Labels := by
  calc
    mixedMoment B raw12364 raw12364Labels = mixedMoment B raw12364step0 raw12364step0Labels := by
      have ha : raw12364step0 = (fun i j => raw12364 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12364step0 raw12364; decide +kernel
      have hl : raw12364step0Labels = raw12364Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12364 raw12364Labels permutation153 permutation3
    mixedMoment B raw12364step0 raw12364step0Labels = mixedMoment B raw12364step1 raw12364step1Labels := by
      have ha : raw12364step1 = raw12364step0 := by apply Matrix.ext; unfold raw12364step1 raw12364step0; decide +kernel
      have hl : raw12364step0Labels = labelEmbedding6 ∘ raw12364step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12364step0 raw12364step0Labels raw12364step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5071 node5071Labels := by rfl

def raw12365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12365step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12365step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12365step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12365step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12365 raw12365Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw12365 raw12365Labels = mixedMoment B raw12365step0 raw12365step0Labels := by
      have hz : ∀ j, raw12365 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12365step0 = (fun i j => raw12365 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12365step0 raw12365; decide +kernel
      have hl : raw12365step0Labels = raw12365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12365 raw12365Labels permutation265 hz
    mixedMoment B raw12365step0 raw12365step0Labels = mixedMoment B raw12365step1 raw12365step1Labels := by
      have ha : raw12365step1 = (fun i j => raw12365step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12365step1 raw12365step0; decide +kernel
      have hl : raw12365step1Labels = raw12365step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12365step0 raw12365step0Labels permutation33 permutation3
    mixedMoment B raw12365step1 raw12365step1Labels = mixedMoment B raw12365step2 raw12365step2Labels := by
      have ha : raw12365step2 = raw12365step1 := by apply Matrix.ext; unfold raw12365step2 raw12365step1; decide +kernel
      have hl : raw12365step1Labels = labelEmbedding6 ∘ raw12365step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12365step1 raw12365step1Labels raw12365step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5164 node5164Labels := by rfl

def raw12366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12366Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12366step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw12366step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12366step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw12366step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12366 raw12366Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw12366 raw12366Labels = mixedMoment B raw12366step0 raw12366step0Labels := by
      have hz : ∀ j, raw12366 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12366step0 = (fun i j => raw12366 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12366step0 raw12366; decide +kernel
      have hl : raw12366step0Labels = raw12366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12366 raw12366Labels permutation265 hz
    mixedMoment B raw12366step0 raw12366step0Labels = mixedMoment B raw12366step1 raw12366step1Labels := by
      have ha : raw12366step1 = (fun i j => raw12366step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12366step1 raw12366step0; decide +kernel
      have hl : raw12366step1Labels = raw12366step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12366step0 raw12366step0Labels permutation39 permutation3
    mixedMoment B raw12366step1 raw12366step1Labels = mixedMoment B raw12366step2 raw12366step2Labels := by
      have ha : raw12366step2 = raw12366step1 := by apply Matrix.ext; unfold raw12366step2 raw12366step1; decide +kernel
      have hl : raw12366step1Labels = labelEmbedding6 ∘ raw12366step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12366step1 raw12366step1Labels raw12366step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5229 node5229Labels := by rfl

def raw12367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw12367Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw12367step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw12367step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12367step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw12367step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12367 raw12367Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw12367 raw12367Labels = mixedMoment B raw12367step0 raw12367step0Labels := by
      have hz : ∀ j, raw12367 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12367step0 = (fun i j => raw12367 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12367step0 raw12367; decide +kernel
      have hl : raw12367step0Labels = raw12367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12367 raw12367Labels permutation265 hz
    mixedMoment B raw12367step0 raw12367step0Labels = mixedMoment B raw12367step1 raw12367step1Labels := by
      have ha : raw12367step1 = (fun i j => raw12367step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12367step1 raw12367step0; decide +kernel
      have hl : raw12367step1Labels = raw12367step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12367step0 raw12367step0Labels permutation36 permutation3
    mixedMoment B raw12367step1 raw12367step1Labels = mixedMoment B raw12367step2 raw12367step2Labels := by
      have ha : raw12367step2 = raw12367step1 := by apply Matrix.ext; unfold raw12367step2 raw12367step1; decide +kernel
      have hl : raw12367step1Labels = labelEmbedding6 ∘ raw12367step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12367step1 raw12367step1Labels raw12367step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw12368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12368Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12368step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12368step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12368step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12368step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12368 raw12368Labels = mixedMoment B node4450 node4450Labels := by
  calc
    mixedMoment B raw12368 raw12368Labels = mixedMoment B raw12368step0 raw12368step0Labels := by
      have hz : ∀ j, raw12368 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12368step0 = (fun i j => raw12368 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12368step0 raw12368; decide +kernel
      have hl : raw12368step0Labels = raw12368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12368 raw12368Labels permutation265 hz
    mixedMoment B raw12368step0 raw12368step0Labels = mixedMoment B raw12368step1 raw12368step1Labels := by
      have ha : raw12368step1 = (fun i j => raw12368step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12368step1 raw12368step0; decide +kernel
      have hl : raw12368step1Labels = raw12368step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12368step0 raw12368step0Labels permutation32 permutation3
    mixedMoment B raw12368step1 raw12368step1Labels = mixedMoment B raw12368step2 raw12368step2Labels := by
      have ha : raw12368step2 = raw12368step1 := by apply Matrix.ext; unfold raw12368step2 raw12368step1; decide +kernel
      have hl : raw12368step1Labels = labelEmbedding6 ∘ raw12368step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12368step1 raw12368step1Labels raw12368step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4450 node4450Labels := by rfl

def raw12369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12369Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12369step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12369step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12369step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12369 raw12369Labels = mixedMoment B node5069 node5069Labels := by
  calc
    mixedMoment B raw12369 raw12369Labels = mixedMoment B raw12369step0 raw12369step0Labels := by
      have ha : raw12369step0 = (fun i j => raw12369 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12369step0 raw12369; decide +kernel
      have hl : raw12369step0Labels = raw12369Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12369 raw12369Labels permutation152 permutation3
    mixedMoment B raw12369step0 raw12369step0Labels = mixedMoment B raw12369step1 raw12369step1Labels := by
      have ha : raw12369step1 = raw12369step0 := by apply Matrix.ext; unfold raw12369step1 raw12369step0; decide +kernel
      have hl : raw12369step0Labels = labelEmbedding6 ∘ raw12369step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12369step0 raw12369step0Labels raw12369step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5069 node5069Labels := by rfl

def raw12370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12370Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12370step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12370step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12370step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12370step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12370 raw12370Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw12370 raw12370Labels = mixedMoment B raw12370step0 raw12370step0Labels := by
      have hz : ∀ j, raw12370 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12370step0 = (fun i j => raw12370 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12370step0 raw12370; decide +kernel
      have hl : raw12370step0Labels = raw12370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12370 raw12370Labels permutation265 hz
    mixedMoment B raw12370step0 raw12370step0Labels = mixedMoment B raw12370step1 raw12370step1Labels := by
      have ha : raw12370step1 = (fun i j => raw12370step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12370step1 raw12370step0; decide +kernel
      have hl : raw12370step1Labels = raw12370step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12370step0 raw12370step0Labels permutation32 permutation3
    mixedMoment B raw12370step1 raw12370step1Labels = mixedMoment B raw12370step2 raw12370step2Labels := by
      have ha : raw12370step2 = raw12370step1 := by apply Matrix.ext; unfold raw12370step2 raw12370step1; decide +kernel
      have hl : raw12370step1Labels = labelEmbedding6 ∘ raw12370step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12370step1 raw12370step1Labels raw12370step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5161 node5161Labels := by rfl

def raw12371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12371Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12371step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw12371step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12371step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw12371step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12371 raw12371Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw12371 raw12371Labels = mixedMoment B raw12371step0 raw12371step0Labels := by
      have hz : ∀ j, raw12371 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12371step0 = (fun i j => raw12371 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12371step0 raw12371; decide +kernel
      have hl : raw12371step0Labels = raw12371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12371 raw12371Labels permutation265 hz
    mixedMoment B raw12371step0 raw12371step0Labels = mixedMoment B raw12371step1 raw12371step1Labels := by
      have ha : raw12371step1 = (fun i j => raw12371step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12371step1 raw12371step0; decide +kernel
      have hl : raw12371step1Labels = raw12371step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12371step0 raw12371step0Labels permutation139 permutation5
    mixedMoment B raw12371step1 raw12371step1Labels = mixedMoment B raw12371step2 raw12371step2Labels := by
      have ha : raw12371step2 = raw12371step1 := by apply Matrix.ext; unfold raw12371step2 raw12371step1; decide +kernel
      have hl : raw12371step1Labels = labelEmbedding8 ∘ raw12371step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12371step1 raw12371step1Labels raw12371step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5140 node5140Labels := by rfl

def raw12372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw12372Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw12372step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12372step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12372step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12372 raw12372Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw12372 raw12372Labels = mixedMoment B raw12372step0 raw12372step0Labels := by
      have hz : ∀ j, raw12372 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12372step0 = (fun i j => raw12372 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12372step0 raw12372; decide +kernel
      have hl : raw12372step0Labels = raw12372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12372 raw12372Labels permutation265 hz
    mixedMoment B raw12372step0 raw12372step0Labels = mixedMoment B raw12372step1 raw12372step1Labels := by
      have ha : raw12372step1 = (fun i j => raw12372step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12372step1 raw12372step0; decide +kernel
      have hl : raw12372step1Labels = raw12372step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12372step0 raw12372step0Labels permutation137 permutation5
    mixedMoment B raw12372step1 raw12372step1Labels = mixedMoment B raw12372step2 raw12372step2Labels := by
      have ha : raw12372step2 = raw12372step1 := by apply Matrix.ext; unfold raw12372step2 raw12372step1; decide +kernel
      have hl : raw12372step1Labels = labelEmbedding8 ∘ raw12372step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12372step1 raw12372step1Labels raw12372step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5161 node5161Labels := by rfl

def raw12373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12373 raw12373Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw12373 raw12373Labels = mixedMoment B raw12373step0 raw12373step0Labels := by
      have ha : raw12373step0 = (fun i j => raw12373 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12373step0 raw12373; decide +kernel
      have hl : raw12373step0Labels = raw12373Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12373 raw12373Labels permutation152 permutation3
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw12374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12374step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12374 raw12374Labels = mixedMoment B node3997 node3997Labels := by
  calc
    mixedMoment B raw12374 raw12374Labels = mixedMoment B raw12374step0 raw12374step0Labels := by
      have hz : ∀ j, raw12374 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12374step0 = (fun i j => raw12374 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12374step0 raw12374; decide +kernel
      have hl : raw12374step0Labels = raw12374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12374 raw12374Labels permutation265 hz
    mixedMoment B raw12374step0 raw12374step0Labels = mixedMoment B raw12374step1 raw12374step1Labels := by
      have ha : raw12374step1 = (fun i j => raw12374step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12374step1 raw12374step0; decide +kernel
      have hl : raw12374step1Labels = raw12374step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12374step0 raw12374step0Labels permutation32 permutation3
    _ = mixedMoment B node3997 node3997Labels := by rfl

def raw12375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12375step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12375step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12375step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12375 raw12375Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw12375 raw12375Labels = mixedMoment B raw12375step0 raw12375step0Labels := by
      have hz : ∀ j, raw12375 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12375step0 = (fun i j => raw12375 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12375step0 raw12375; decide +kernel
      have hl : raw12375step0Labels = raw12375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12375 raw12375Labels permutation265 hz
    mixedMoment B raw12375step0 raw12375step0Labels = mixedMoment B raw12375step1 raw12375step1Labels := by
      have ha : raw12375step1 = (fun i j => raw12375step0 (permutation92 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12375step1 raw12375step0; decide +kernel
      have hl : raw12375step1Labels = raw12375step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12375step0 raw12375step0Labels permutation92 permutation6
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw12376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12376 raw12376Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw12376 raw12376Labels = mixedMoment B raw12376step0 raw12376step0Labels := by
      have hz : ∀ j, raw12376 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12376step0 = (fun i j => raw12376 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12376step0 raw12376; decide +kernel
      have hl : raw12376step0Labels = raw12376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12376 raw12376Labels permutation265 hz
    mixedMoment B raw12376step0 raw12376step0Labels = mixedMoment B raw12376step1 raw12376step1Labels := by
      have ha : raw12376step1 = (fun i j => raw12376step0 (permutation92 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12376step1 raw12376step0; decide +kernel
      have hl : raw12376step1Labels = raw12376step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12376step0 raw12376step0Labels permutation92 permutation6
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw12377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12377step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12377 raw12377Labels = mixedMoment B node3998 node3998Labels := by
  calc
    mixedMoment B raw12377 raw12377Labels = mixedMoment B raw12377step0 raw12377step0Labels := by
      have hz : ∀ j, raw12377 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12377step0 = (fun i j => raw12377 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12377step0 raw12377; decide +kernel
      have hl : raw12377step0Labels = raw12377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12377 raw12377Labels permutation265 hz
    mixedMoment B raw12377step0 raw12377step0Labels = mixedMoment B raw12377step1 raw12377step1Labels := by
      have ha : raw12377step1 = (fun i j => raw12377step0 (permutation92 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12377step1 raw12377step0; decide +kernel
      have hl : raw12377step1Labels = raw12377step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12377step0 raw12377step0Labels permutation92 permutation6
    _ = mixedMoment B node3998 node3998Labels := by rfl

def raw12378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12378 raw12378Labels = mixedMoment B node1032 node1032Labels := by
  calc
    mixedMoment B raw12378 raw12378Labels = mixedMoment B raw12378step0 raw12378step0Labels := by
      have ha : raw12378step0 = (fun i j => raw12378 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12378step0 raw12378; decide +kernel
      have hl : raw12378step0Labels = raw12378Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12378 raw12378Labels permutation184 permutation3
    _ = mixedMoment B node1032 node1032Labels := by rfl

def raw12379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12379step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12379 raw12379Labels = mixedMoment B node2587 node2587Labels := by
  calc
    mixedMoment B raw12379 raw12379Labels = mixedMoment B raw12379step0 raw12379step0Labels := by
      have ha : raw12379step0 = (fun i j => raw12379 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12379step0 raw12379; decide +kernel
      have hl : raw12379step0Labels = raw12379Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12379 raw12379Labels permutation184 permutation3
    _ = mixedMoment B node2587 node2587Labels := by rfl

def raw12380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12380Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12380 raw12380Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw12380 raw12380Labels = mixedMoment B raw12380step0 raw12380step0Labels := by
      have ha : raw12380step0 = (fun i j => raw12380 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12380step0 raw12380; decide +kernel
      have hl : raw12380step0Labels = raw12380Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12380 raw12380Labels permutation208 permutation3
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw12381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12381Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12381 raw12381Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw12381 raw12381Labels = mixedMoment B raw12381step0 raw12381step0Labels := by
      have ha : raw12381step0 = (fun i j => raw12381 (permutation232 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12381step0 raw12381; decide +kernel
      have hl : raw12381step0Labels = raw12381Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12381 raw12381Labels permutation232 permutation3
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw12382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12382step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12382 raw12382Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw12382 raw12382Labels = mixedMoment B raw12382step0 raw12382step0Labels := by
      have ha : raw12382step0 = (fun i j => raw12382 (permutation197 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12382step0 raw12382; decide +kernel
      have hl : raw12382step0Labels = raw12382Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12382 raw12382Labels permutation197 permutation3
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw12383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12383step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12383 raw12383Labels = mixedMoment B node1071 node1071Labels := by
  calc
    mixedMoment B raw12383 raw12383Labels = mixedMoment B raw12383step0 raw12383step0Labels := by
      have hz : ∀ j, raw12383 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12383step0 = (fun i j => raw12383 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12383step0 raw12383; decide +kernel
      have hl : raw12383step0Labels = raw12383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12383 raw12383Labels permutation265 hz
    mixedMoment B raw12383step0 raw12383step0Labels = mixedMoment B raw12383step1 raw12383step1Labels := by
      have ha : raw12383step1 = (fun i j => raw12383step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12383step1 raw12383step0; decide +kernel
      have hl : raw12383step1Labels = raw12383step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12383step0 raw12383step0Labels permutation40 permutation3
    _ = mixedMoment B node1071 node1071Labels := by rfl

def raw12384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12384Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12384step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12384 raw12384Labels = mixedMoment B node2501 node2501Labels := by
  calc
    mixedMoment B raw12384 raw12384Labels = mixedMoment B raw12384step0 raw12384step0Labels := by
      have ha : raw12384step0 = (fun i j => raw12384 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12384step0 raw12384; decide +kernel
      have hl : raw12384step0Labels = raw12384Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12384 raw12384Labels permutation160 permutation3
    _ = mixedMoment B node2501 node2501Labels := by rfl

def raw12385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12385Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12385step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw12385step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12385 raw12385Labels = mixedMoment B node2682 node2682Labels := by
  calc
    mixedMoment B raw12385 raw12385Labels = mixedMoment B raw12385step0 raw12385step0Labels := by
      have hz : ∀ j, raw12385 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12385step0 = (fun i j => raw12385 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12385step0 raw12385; decide +kernel
      have hl : raw12385step0Labels = raw12385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12385 raw12385Labels permutation265 hz
    mixedMoment B raw12385step0 raw12385step0Labels = mixedMoment B raw12385step1 raw12385step1Labels := by
      have ha : raw12385step1 = (fun i j => raw12385step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12385step1 raw12385step0; decide +kernel
      have hl : raw12385step1Labels = raw12385step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12385step0 raw12385step0Labels permutation40 permutation3
    _ = mixedMoment B node2682 node2682Labels := by rfl

def raw12386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12386Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12386step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw12386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12386 raw12386Labels = mixedMoment B node2736 node2736Labels := by
  calc
    mixedMoment B raw12386 raw12386Labels = mixedMoment B raw12386step0 raw12386step0Labels := by
      have hz : ∀ j, raw12386 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12386step0 = (fun i j => raw12386 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12386step0 raw12386; decide +kernel
      have hl : raw12386step0Labels = raw12386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12386 raw12386Labels permutation265 hz
    mixedMoment B raw12386step0 raw12386step0Labels = mixedMoment B raw12386step1 raw12386step1Labels := by
      have ha : raw12386step1 = (fun i j => raw12386step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12386step1 raw12386step0; decide +kernel
      have hl : raw12386step1Labels = raw12386step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12386step0 raw12386step0Labels permutation46 permutation3
    _ = mixedMoment B node2736 node2736Labels := by rfl

def raw12387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12387Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12387step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12387step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12387 raw12387Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw12387 raw12387Labels = mixedMoment B raw12387step0 raw12387step0Labels := by
      have hz : ∀ j, raw12387 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12387step0 = (fun i j => raw12387 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12387step0 raw12387; decide +kernel
      have hl : raw12387step0Labels = raw12387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12387 raw12387Labels permutation265 hz
    mixedMoment B raw12387step0 raw12387step0Labels = mixedMoment B raw12387step1 raw12387step1Labels := by
      have ha : raw12387step1 = (fun i j => raw12387step0 (permutation53 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12387step1 raw12387step0; decide +kernel
      have hl : raw12387step1Labels = raw12387step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12387step0 raw12387step0Labels permutation53 permutation3
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw12388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12388Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12388step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12388step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12388 raw12388Labels = mixedMoment B node1042 node1042Labels := by
  calc
    mixedMoment B raw12388 raw12388Labels = mixedMoment B raw12388step0 raw12388step0Labels := by
      have hz : ∀ j, raw12388 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12388step0 = (fun i j => raw12388 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12388step0 raw12388; decide +kernel
      have hl : raw12388step0Labels = raw12388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12388 raw12388Labels permutation265 hz
    mixedMoment B raw12388step0 raw12388step0Labels = mixedMoment B raw12388step1 raw12388step1Labels := by
      have ha : raw12388step1 = (fun i j => raw12388step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12388step1 raw12388step0; decide +kernel
      have hl : raw12388step1Labels = raw12388step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12388step0 raw12388step0Labels permutation35 permutation3
    _ = mixedMoment B node1042 node1042Labels := by rfl

def raw12389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12389Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12389step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12389 raw12389Labels = mixedMoment B node2481 node2481Labels := by
  calc
    mixedMoment B raw12389 raw12389Labels = mixedMoment B raw12389step0 raw12389step0Labels := by
      have ha : raw12389step0 = (fun i j => raw12389 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12389step0 raw12389; decide +kernel
      have hl : raw12389step0Labels = raw12389Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12389 raw12389Labels permutation155 permutation3
    _ = mixedMoment B node2481 node2481Labels := by rfl

def raw12390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12390Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12390step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12390step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw12390step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12390 raw12390Labels = mixedMoment B node2596 node2596Labels := by
  calc
    mixedMoment B raw12390 raw12390Labels = mixedMoment B raw12390step0 raw12390step0Labels := by
      have hz : ∀ j, raw12390 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12390step0 = (fun i j => raw12390 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12390step0 raw12390; decide +kernel
      have hl : raw12390step0Labels = raw12390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12390 raw12390Labels permutation265 hz
    mixedMoment B raw12390step0 raw12390step0Labels = mixedMoment B raw12390step1 raw12390step1Labels := by
      have ha : raw12390step1 = (fun i j => raw12390step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12390step1 raw12390step0; decide +kernel
      have hl : raw12390step1Labels = raw12390step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12390step0 raw12390step0Labels permutation35 permutation3
    _ = mixedMoment B node2596 node2596Labels := by rfl

def raw12391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12391Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12391step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw12391step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12391 raw12391Labels = mixedMoment B node2724 node2724Labels := by
  calc
    mixedMoment B raw12391 raw12391Labels = mixedMoment B raw12391step0 raw12391step0Labels := by
      have hz : ∀ j, raw12391 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12391step0 = (fun i j => raw12391 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12391step0 raw12391; decide +kernel
      have hl : raw12391step0Labels = raw12391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12391 raw12391Labels permutation265 hz
    mixedMoment B raw12391step0 raw12391step0Labels = mixedMoment B raw12391step1 raw12391step1Labels := by
      have ha : raw12391step1 = (fun i j => raw12391step0 (permutation45 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12391step1 raw12391step0; decide +kernel
      have hl : raw12391step1Labels = raw12391step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12391step0 raw12391step0Labels permutation45 permutation3
    _ = mixedMoment B node2724 node2724Labels := by rfl

def raw12392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12392Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12392step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12392step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw12392step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12392 raw12392Labels = mixedMoment B node2753 node2753Labels := by
  calc
    mixedMoment B raw12392 raw12392Labels = mixedMoment B raw12392step0 raw12392step0Labels := by
      have hz : ∀ j, raw12392 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12392step0 = (fun i j => raw12392 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12392step0 raw12392; decide +kernel
      have hl : raw12392step0Labels = raw12392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12392 raw12392Labels permutation265 hz
    mixedMoment B raw12392step0 raw12392step0Labels = mixedMoment B raw12392step1 raw12392step1Labels := by
      have ha : raw12392step1 = (fun i j => raw12392step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12392step1 raw12392step0; decide +kernel
      have hl : raw12392step1Labels = raw12392step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12392step0 raw12392step0Labels permutation37 permutation3
    _ = mixedMoment B node2753 node2753Labels := by rfl

def raw12393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12393Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12393step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12393step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12393 raw12393Labels = mixedMoment B node1036 node1036Labels := by
  calc
    mixedMoment B raw12393 raw12393Labels = mixedMoment B raw12393step0 raw12393step0Labels := by
      have hz : ∀ j, raw12393 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12393step0 = (fun i j => raw12393 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12393step0 raw12393; decide +kernel
      have hl : raw12393step0Labels = raw12393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12393 raw12393Labels permutation265 hz
    mixedMoment B raw12393step0 raw12393step0Labels = mixedMoment B raw12393step1 raw12393step1Labels := by
      have ha : raw12393step1 = (fun i j => raw12393step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12393step1 raw12393step0; decide +kernel
      have hl : raw12393step1Labels = raw12393step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12393step0 raw12393step0Labels permutation33 permutation3
    _ = mixedMoment B node1036 node1036Labels := by rfl

def raw12394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12394Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12394step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12394 raw12394Labels = mixedMoment B node2478 node2478Labels := by
  calc
    mixedMoment B raw12394 raw12394Labels = mixedMoment B raw12394step0 raw12394step0Labels := by
      have ha : raw12394step0 = (fun i j => raw12394 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12394step0 raw12394; decide +kernel
      have hl : raw12394step0Labels = raw12394Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12394 raw12394Labels permutation153 permutation3
    _ = mixedMoment B node2478 node2478Labels := by rfl

def raw12395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12395Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12395step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw12395step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12395 raw12395Labels = mixedMoment B node2591 node2591Labels := by
  calc
    mixedMoment B raw12395 raw12395Labels = mixedMoment B raw12395step0 raw12395step0Labels := by
      have hz : ∀ j, raw12395 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12395step0 = (fun i j => raw12395 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12395step0 raw12395; decide +kernel
      have hl : raw12395step0Labels = raw12395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12395 raw12395Labels permutation265 hz
    mixedMoment B raw12395step0 raw12395step0Labels = mixedMoment B raw12395step1 raw12395step1Labels := by
      have ha : raw12395step1 = (fun i j => raw12395step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12395step1 raw12395step0; decide +kernel
      have hl : raw12395step1Labels = raw12395step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12395step0 raw12395step0Labels permutation33 permutation3
    _ = mixedMoment B node2591 node2591Labels := by rfl

def raw12396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12396Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![1, -2, 1]]
def raw12396step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw12396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12396 raw12396Labels = mixedMoment B node2673 node2673Labels := by
  calc
    mixedMoment B raw12396 raw12396Labels = mixedMoment B raw12396step0 raw12396step0Labels := by
      have hz : ∀ j, raw12396 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12396step0 = (fun i j => raw12396 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12396step0 raw12396; decide +kernel
      have hl : raw12396step0Labels = raw12396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12396 raw12396Labels permutation265 hz
    mixedMoment B raw12396step0 raw12396step0Labels = mixedMoment B raw12396step1 raw12396step1Labels := by
      have ha : raw12396step1 = (fun i j => raw12396step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12396step1 raw12396step0; decide +kernel
      have hl : raw12396step1Labels = raw12396step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12396step0 raw12396step0Labels permutation39 permutation3
    _ = mixedMoment B node2673 node2673Labels := by rfl

def raw12397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw12397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1], ![0, -1, 1]]
def raw12397step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12397step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw12397step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12397 raw12397Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw12397 raw12397Labels = mixedMoment B raw12397step0 raw12397step0Labels := by
      have hz : ∀ j, raw12397 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12397step0 = (fun i j => raw12397 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12397step0 raw12397; decide +kernel
      have hl : raw12397step0Labels = raw12397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12397 raw12397Labels permutation265 hz
    mixedMoment B raw12397step0 raw12397step0Labels = mixedMoment B raw12397step1 raw12397step1Labels := by
      have ha : raw12397step1 = (fun i j => raw12397step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12397step1 raw12397step0; decide +kernel
      have hl : raw12397step1Labels = raw12397step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12397step0 raw12397step0Labels permutation36 permutation3
    _ = mixedMoment B node2751 node2751Labels := by rfl

def raw12398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12398step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12398 raw12398Labels = mixedMoment B node1033 node1033Labels := by
  calc
    mixedMoment B raw12398 raw12398Labels = mixedMoment B raw12398step0 raw12398step0Labels := by
      have hz : ∀ j, raw12398 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12398step0 = (fun i j => raw12398 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12398step0 raw12398; decide +kernel
      have hl : raw12398step0Labels = raw12398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12398 raw12398Labels permutation265 hz
    mixedMoment B raw12398step0 raw12398step0Labels = mixedMoment B raw12398step1 raw12398step1Labels := by
      have ha : raw12398step1 = (fun i j => raw12398step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12398step1 raw12398step0; decide +kernel
      have hl : raw12398step1Labels = raw12398step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12398step0 raw12398step0Labels permutation32 permutation3
    _ = mixedMoment B node1033 node1033Labels := by rfl

def raw12399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12399Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12399step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12399 raw12399Labels = mixedMoment B node2476 node2476Labels := by
  calc
    mixedMoment B raw12399 raw12399Labels = mixedMoment B raw12399step0 raw12399step0Labels := by
      have ha : raw12399step0 = (fun i j => raw12399 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12399step0 raw12399; decide +kernel
      have hl : raw12399step0Labels = raw12399Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12399 raw12399Labels permutation152 permutation3
    _ = mixedMoment B node2476 node2476Labels := by rfl

def raw12400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12400Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12400step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw12400step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12400 raw12400Labels = mixedMoment B node2588 node2588Labels := by
  calc
    mixedMoment B raw12400 raw12400Labels = mixedMoment B raw12400step0 raw12400step0Labels := by
      have hz : ∀ j, raw12400 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12400step0 = (fun i j => raw12400 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12400step0 raw12400; decide +kernel
      have hl : raw12400step0Labels = raw12400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12400 raw12400Labels permutation265 hz
    mixedMoment B raw12400step0 raw12400step0Labels = mixedMoment B raw12400step1 raw12400step1Labels := by
      have ha : raw12400step1 = (fun i j => raw12400step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12400step1 raw12400step0; decide +kernel
      have hl : raw12400step1Labels = raw12400step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12400step0 raw12400step0Labels permutation32 permutation3
    _ = mixedMoment B node2588 node2588Labels := by rfl

def raw12401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw12401step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw12401step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12401 raw12401Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw12401 raw12401Labels = mixedMoment B raw12401step0 raw12401step0Labels := by
      have hz : ∀ j, raw12401 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12401step0 = (fun i j => raw12401 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12401step0 raw12401; decide +kernel
      have hl : raw12401step0Labels = raw12401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12401 raw12401Labels permutation265 hz
    mixedMoment B raw12401step0 raw12401step0Labels = mixedMoment B raw12401step1 raw12401step1Labels := by
      have ha : raw12401step1 = (fun i j => raw12401step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12401step1 raw12401step0; decide +kernel
      have hl : raw12401step1Labels = raw12401step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12401step0 raw12401step0Labels permutation38 permutation3
    _ = mixedMoment B node2670 node2670Labels := by rfl

def raw12402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw12402Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw12402step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw12402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12402 raw12402Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw12402 raw12402Labels = mixedMoment B raw12402step0 raw12402step0Labels := by
      have hz : ∀ j, raw12402 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12402step0 = (fun i j => raw12402 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12402step0 raw12402; decide +kernel
      have hl : raw12402step0Labels = raw12402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12402 raw12402Labels permutation265 hz
    mixedMoment B raw12402step0 raw12402step0Labels = mixedMoment B raw12402step1 raw12402step1Labels := by
      have ha : raw12402step1 = (fun i j => raw12402step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12402step1 raw12402step0; decide +kernel
      have hl : raw12402step1Labels = raw12402step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12402step0 raw12402step0Labels permutation44 permutation3
    _ = mixedMoment B node2719 node2719Labels := by rfl

def raw12403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12403Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12403step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12403step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12403 raw12403Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw12403 raw12403Labels = mixedMoment B raw12403step0 raw12403step0Labels := by
      have ha : raw12403step0 = (fun i j => raw12403 (permutation494 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12403step0 raw12403; decide +kernel
      have hl : raw12403step0Labels = raw12403Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12403 raw12403Labels permutation494 permutation7
    mixedMoment B raw12403step0 raw12403step0Labels = mixedMoment B raw12403step1 raw12403step1Labels := by
      have ha : raw12403step1 = raw12403step0 := by apply Matrix.ext; unfold raw12403step1 raw12403step0; decide +kernel
      have hl : raw12403step0Labels = labelEmbedding1 ∘ raw12403step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12403step0 raw12403step0Labels raw12403step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw12404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12404Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12404step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12404step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12404step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw12404step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12404 raw12404Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw12404 raw12404Labels = mixedMoment B raw12404step0 raw12404step0Labels := by
      have hz : ∀ j, raw12404 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12404step0 = (fun i j => raw12404 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12404step0 raw12404; decide +kernel
      have hl : raw12404step0Labels = raw12404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12404 raw12404Labels permutation265 hz
    mixedMoment B raw12404step0 raw12404step0Labels = mixedMoment B raw12404step1 raw12404step1Labels := by
      have ha : raw12404step1 = (fun i j => raw12404step0 (permutation97 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12404step1 raw12404step0; decide +kernel
      have hl : raw12404step1Labels = raw12404step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12404step0 raw12404step0Labels permutation97 permutation7
    mixedMoment B raw12404step1 raw12404step1Labels = mixedMoment B raw12404step2 raw12404step2Labels := by
      have ha : raw12404step2 = raw12404step1 := by apply Matrix.ext; unfold raw12404step2 raw12404step1; decide +kernel
      have hl : raw12404step1Labels = labelEmbedding1 ∘ raw12404step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12404step1 raw12404step1Labels raw12404step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw12405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12405Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12405step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12405step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12405step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12405step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw12405step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12405 raw12405Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw12405 raw12405Labels = mixedMoment B raw12405step0 raw12405step0Labels := by
      have hz : ∀ j, raw12405 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12405step0 = (fun i j => raw12405 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12405step0 raw12405; decide +kernel
      have hl : raw12405step0Labels = raw12405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12405 raw12405Labels permutation265 hz
    mixedMoment B raw12405step0 raw12405step0Labels = mixedMoment B raw12405step1 raw12405step1Labels := by
      have ha : raw12405step1 = (fun i j => raw12405step0 (permutation138 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12405step1 raw12405step0; decide +kernel
      have hl : raw12405step1Labels = raw12405step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12405step0 raw12405step0Labels permutation138 permutation5
    mixedMoment B raw12405step1 raw12405step1Labels = mixedMoment B raw12405step2 raw12405step2Labels := by
      have ha : raw12405step2 = raw12405step1 := by apply Matrix.ext; unfold raw12405step2 raw12405step1; decide +kernel
      have hl : raw12405step1Labels = labelEmbedding1 ∘ raw12405step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12405step1 raw12405step1Labels raw12405step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw12406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12406Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12406step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12406step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12406step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw12406step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12406 raw12406Labels = mixedMoment B node3997 node3997Labels := by
  calc
    mixedMoment B raw12406 raw12406Labels = mixedMoment B raw12406step0 raw12406step0Labels := by
      have hz : ∀ j, raw12406 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12406step0 = (fun i j => raw12406 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12406step0 raw12406; decide +kernel
      have hl : raw12406step0Labels = raw12406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12406 raw12406Labels permutation265 hz
    mixedMoment B raw12406step0 raw12406step0Labels = mixedMoment B raw12406step1 raw12406step1Labels := by
      have ha : raw12406step1 = (fun i j => raw12406step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12406step1 raw12406step0; decide +kernel
      have hl : raw12406step1Labels = raw12406step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12406step0 raw12406step0Labels permutation137 permutation5
    mixedMoment B raw12406step1 raw12406step1Labels = mixedMoment B raw12406step2 raw12406step2Labels := by
      have ha : raw12406step2 = raw12406step1 := by apply Matrix.ext; unfold raw12406step2 raw12406step1; decide +kernel
      have hl : raw12406step1Labels = labelEmbedding1 ∘ raw12406step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12406step1 raw12406step1Labels raw12406step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3997 node3997Labels := by rfl

def raw12407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12407Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12407step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12407step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12407step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12407 raw12407Labels = mixedMoment B node3984 node3984Labels := by
  calc
    mixedMoment B raw12407 raw12407Labels = mixedMoment B raw12407step0 raw12407step0Labels := by
      have hz : ∀ j, raw12407 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12407step0 = (fun i j => raw12407 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12407step0 raw12407; decide +kernel
      have hl : raw12407step0Labels = raw12407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12407 raw12407Labels permutation265 hz
    mixedMoment B raw12407step0 raw12407step0Labels = mixedMoment B raw12407step1 raw12407step1Labels := by
      have ha : raw12407step1 = (fun i j => raw12407step0 (permutation95 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12407step1 raw12407step0; decide +kernel
      have hl : raw12407step1Labels = raw12407step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12407step0 raw12407step0Labels permutation95 permutation7
    mixedMoment B raw12407step1 raw12407step1Labels = mixedMoment B raw12407step2 raw12407step2Labels := by
      have ha : raw12407step2 = raw12407step1 := by apply Matrix.ext; unfold raw12407step2 raw12407step1; decide +kernel
      have hl : raw12407step1Labels = labelEmbedding1 ∘ raw12407step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12407step1 raw12407step1Labels raw12407step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3984 node3984Labels := by rfl

def raw12408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12408Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw12408step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12408step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12408step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12408 raw12408Labels = mixedMoment B node1636 node1636Labels := by
  calc
    mixedMoment B raw12408 raw12408Labels = mixedMoment B raw12408step0 raw12408step0Labels := by
      have ha : raw12408step0 = (fun i j => raw12408 (permutation214 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12408step0 raw12408; decide +kernel
      have hl : raw12408step0Labels = raw12408Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12408 raw12408Labels permutation214 permutation5
    mixedMoment B raw12408step0 raw12408step0Labels = mixedMoment B raw12408step1 raw12408step1Labels := by
      have ha : raw12408step1 = -raw12408step0 := by apply Matrix.ext; change ∀ i j, raw12408step1 i j = -(raw12408step0 i j); unfold raw12408step1 raw12408step0; decide +kernel
      have hl : raw12408step1Labels = raw12408step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12408step1 raw12408step1Labels = mixedMoment B raw12408step2 raw12408step2Labels := by
      have ha : raw12408step2 = raw12408step1 := by apply Matrix.ext; unfold raw12408step2 raw12408step1; decide +kernel
      have hl : raw12408step1Labels = labelEmbedding1 ∘ raw12408step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12408step1 raw12408step1Labels raw12408step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1636 node1636Labels := by rfl

def raw12409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12409Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw12409step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12409step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12409step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12409step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw12409step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12409 raw12409Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw12409 raw12409Labels = mixedMoment B raw12409step0 raw12409step0Labels := by
      have ha : raw12409step0 = (fun i j => raw12409 (permutation208 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12409step0 raw12409; decide +kernel
      have hl : raw12409step0Labels = raw12409Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12409 raw12409Labels permutation208 permutation5
    mixedMoment B raw12409step0 raw12409step0Labels = mixedMoment B raw12409step1 raw12409step1Labels := by
      have ha : raw12409step1 = -raw12409step0 := by apply Matrix.ext; change ∀ i j, raw12409step1 i j = -(raw12409step0 i j); unfold raw12409step1 raw12409step0; decide +kernel
      have hl : raw12409step1Labels = raw12409step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12409step1 raw12409step1Labels = mixedMoment B raw12409step2 raw12409step2Labels := by
      have ha : raw12409step2 = raw12409step1 := by apply Matrix.ext; unfold raw12409step2 raw12409step1; decide +kernel
      have hl : raw12409step1Labels = labelEmbedding1 ∘ raw12409step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12409step1 raw12409step1Labels raw12409step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

def raw12410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12410Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw12410step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12410step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12410step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12410step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12410step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12410 raw12410Labels = mixedMoment B node3376 node3376Labels := by
  calc
    mixedMoment B raw12410 raw12410Labels = mixedMoment B raw12410step0 raw12410step0Labels := by
      have ha : raw12410step0 = (fun i j => raw12410 (permutation214 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12410step0 raw12410; decide +kernel
      have hl : raw12410step0Labels = raw12410Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12410 raw12410Labels permutation214 permutation5
    mixedMoment B raw12410step0 raw12410step0Labels = mixedMoment B raw12410step1 raw12410step1Labels := by
      have ha : raw12410step1 = -raw12410step0 := by apply Matrix.ext; change ∀ i j, raw12410step1 i j = -(raw12410step0 i j); unfold raw12410step1 raw12410step0; decide +kernel
      have hl : raw12410step1Labels = raw12410step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12410step1 raw12410step1Labels = mixedMoment B raw12410step2 raw12410step2Labels := by
      have ha : raw12410step2 = raw12410step1 := by apply Matrix.ext; unfold raw12410step2 raw12410step1; decide +kernel
      have hl : raw12410step1Labels = labelEmbedding1 ∘ raw12410step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12410step1 raw12410step1Labels raw12410step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3376 node3376Labels := by rfl

def raw12411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![0, 1, -1], ![1, -2, 1]]
def raw12411Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw12411step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12411step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12411step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12411step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12411 raw12411Labels = mixedMoment B node3503 node3503Labels := by
  calc
    mixedMoment B raw12411 raw12411Labels = mixedMoment B raw12411step0 raw12411step0Labels := by
      have ha : raw12411step0 = (fun i j => raw12411 (permutation236 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12411step0 raw12411; decide +kernel
      have hl : raw12411step0Labels = raw12411Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12411 raw12411Labels permutation236 permutation5
    mixedMoment B raw12411step0 raw12411step0Labels = mixedMoment B raw12411step1 raw12411step1Labels := by
      have ha : raw12411step1 = -raw12411step0 := by apply Matrix.ext; change ∀ i j, raw12411step1 i j = -(raw12411step0 i j); unfold raw12411step1 raw12411step0; decide +kernel
      have hl : raw12411step1Labels = raw12411step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12411step1 raw12411step1Labels = mixedMoment B raw12411step2 raw12411step2Labels := by
      have ha : raw12411step2 = raw12411step1 := by apply Matrix.ext; unfold raw12411step2 raw12411step1; decide +kernel
      have hl : raw12411step1Labels = labelEmbedding1 ∘ raw12411step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12411step1 raw12411step1Labels raw12411step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3503 node3503Labels := by rfl

def raw12412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![0, -1, 1]]
def raw12412Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw12412step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12412step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12412step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12412step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12412step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12412 raw12412Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw12412 raw12412Labels = mixedMoment B raw12412step0 raw12412step0Labels := by
      have ha : raw12412step0 = (fun i j => raw12412 (permutation215 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12412step0 raw12412; decide +kernel
      have hl : raw12412step0Labels = raw12412Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12412 raw12412Labels permutation215 permutation5
    mixedMoment B raw12412step0 raw12412step0Labels = mixedMoment B raw12412step1 raw12412step1Labels := by
      have ha : raw12412step1 = -raw12412step0 := by apply Matrix.ext; change ∀ i j, raw12412step1 i j = -(raw12412step0 i j); unfold raw12412step1 raw12412step0; decide +kernel
      have hl : raw12412step1Labels = raw12412step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12412step1 raw12412step1Labels = mixedMoment B raw12412step2 raw12412step2Labels := by
      have ha : raw12412step2 = raw12412step1 := by apply Matrix.ext; unfold raw12412step2 raw12412step1; decide +kernel
      have hl : raw12412step1Labels = labelEmbedding1 ∘ raw12412step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12412step1 raw12412step1Labels raw12412step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3571 node3571Labels := by rfl

def raw12413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12413Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12413step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw12413step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12413step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw12413step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12413step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw12413step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12413 raw12413Labels = mixedMoment B node1641 node1641Labels := by
  calc
    mixedMoment B raw12413 raw12413Labels = mixedMoment B raw12413step0 raw12413step0Labels := by
      have hz : ∀ j, raw12413 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12413step0 = (fun i j => raw12413 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12413step0 raw12413; decide +kernel
      have hl : raw12413step0Labels = raw12413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12413 raw12413Labels permutation265 hz
    mixedMoment B raw12413step0 raw12413step0Labels = mixedMoment B raw12413step1 raw12413step1Labels := by
      have ha : raw12413step1 = (fun i j => raw12413step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12413step1 raw12413step0; decide +kernel
      have hl : raw12413step1Labels = raw12413step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12413step0 raw12413step0Labels permutation40 permutation5
    mixedMoment B raw12413step1 raw12413step1Labels = mixedMoment B raw12413step2 raw12413step2Labels := by
      have ha : raw12413step2 = -raw12413step1 := by apply Matrix.ext; change ∀ i j, raw12413step2 i j = -(raw12413step1 i j); unfold raw12413step2 raw12413step1; decide +kernel
      have hl : raw12413step2Labels = raw12413step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12413step2 raw12413step2Labels = mixedMoment B raw12413step3 raw12413step3Labels := by
      have ha : raw12413step3 = raw12413step2 := by apply Matrix.ext; unfold raw12413step3 raw12413step2; decide +kernel
      have hl : raw12413step2Labels = labelEmbedding1 ∘ raw12413step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12413step2 raw12413step2Labels raw12413step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1641 node1641Labels := by rfl

def raw12414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12414Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw12414step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12414step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw12414step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12414step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw12414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12414 raw12414Labels = mixedMoment B node3442 node3442Labels := by
  calc
    mixedMoment B raw12414 raw12414Labels = mixedMoment B raw12414step0 raw12414step0Labels := by
      have ha : raw12414step0 = (fun i j => raw12414 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12414step0 raw12414; decide +kernel
      have hl : raw12414step0Labels = raw12414Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12414 raw12414Labels permutation160 permutation5
    mixedMoment B raw12414step0 raw12414step0Labels = mixedMoment B raw12414step1 raw12414step1Labels := by
      have ha : raw12414step1 = -raw12414step0 := by apply Matrix.ext; change ∀ i j, raw12414step1 i j = -(raw12414step0 i j); unfold raw12414step1 raw12414step0; decide +kernel
      have hl : raw12414step1Labels = raw12414step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12414step1 raw12414step1Labels = mixedMoment B raw12414step2 raw12414step2Labels := by
      have ha : raw12414step2 = raw12414step1 := by apply Matrix.ext; unfold raw12414step2 raw12414step1; decide +kernel
      have hl : raw12414step1Labels = labelEmbedding1 ∘ raw12414step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12414step1 raw12414step1Labels raw12414step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3442 node3442Labels := by rfl

def raw12415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12415Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 2, -2], ![1, 0, -1], ![1, -2, 1]]
def raw12415step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw12415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw12415step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12415step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw12415step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw12415step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw12415step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12415 raw12415Labels = mixedMoment B node3380 node3380Labels := by
  calc
    mixedMoment B raw12415 raw12415Labels = mixedMoment B raw12415step0 raw12415step0Labels := by
      have hz : ∀ j, raw12415 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12415step0 = (fun i j => raw12415 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12415step0 raw12415; decide +kernel
      have hl : raw12415step0Labels = raw12415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12415 raw12415Labels permutation265 hz
    mixedMoment B raw12415step0 raw12415step0Labels = mixedMoment B raw12415step1 raw12415step1Labels := by
      have ha : raw12415step1 = (fun i j => raw12415step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12415step1 raw12415step0; decide +kernel
      have hl : raw12415step1Labels = raw12415step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12415step0 raw12415step0Labels permutation40 permutation5
    mixedMoment B raw12415step1 raw12415step1Labels = mixedMoment B raw12415step2 raw12415step2Labels := by
      have ha : raw12415step2 = -raw12415step1 := by apply Matrix.ext; change ∀ i j, raw12415step2 i j = -(raw12415step1 i j); unfold raw12415step2 raw12415step1; decide +kernel
      have hl : raw12415step2Labels = raw12415step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12415step2 raw12415step2Labels = mixedMoment B raw12415step3 raw12415step3Labels := by
      have ha : raw12415step3 = raw12415step2 := by apply Matrix.ext; unfold raw12415step3 raw12415step2; decide +kernel
      have hl : raw12415step2Labels = labelEmbedding1 ∘ raw12415step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12415step2 raw12415step2Labels raw12415step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3380 node3380Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
