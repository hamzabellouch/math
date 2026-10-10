import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw42240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42240Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42240step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42240step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42240step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42240step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42240step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42240 raw42240Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw42240 raw42240Labels = mixedMoment B raw42240step0 raw42240step0Labels := by
      have ha : raw42240step0 = (fun i j => raw42240 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42240step0 raw42240; decide +kernel
      have hl : raw42240step0Labels = raw42240Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42240 raw42240Labels permutation682 permutation2
    mixedMoment B raw42240step0 raw42240step0Labels = mixedMoment B raw42240step1 raw42240step1Labels := by
      have ha : raw42240step1 = -raw42240step0 := by apply Matrix.ext; change ∀ i j, raw42240step1 i j = -(raw42240step0 i j); unfold raw42240step1 raw42240step0; decide +kernel
      have hl : raw42240step1Labels = raw42240step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42240step1 raw42240step1Labels = mixedMoment B raw42240step2 raw42240step2Labels := by
      have ha : raw42240step2 = raw42240step1 := by apply Matrix.ext; unfold raw42240step2 raw42240step1; decide +kernel
      have hl : raw42240step1Labels = labelEmbedding1 ∘ raw42240step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42240step1 raw42240step1Labels raw42240step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

def raw42241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42241Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42241step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42241step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42241 raw42241Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw42241 raw42241Labels = mixedMoment B raw42241step0 raw42241step0Labels := by
      have ha : raw42241step0 = (fun i j => raw42241 (permutation646 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42241step0 raw42241; decide +kernel
      have hl : raw42241step0Labels = raw42241Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42241 raw42241Labels permutation646 permutation7
    mixedMoment B raw42241step0 raw42241step0Labels = mixedMoment B raw42241step1 raw42241step1Labels := by
      have ha : raw42241step1 = raw42241step0 := by apply Matrix.ext; unfold raw42241step1 raw42241step0; decide +kernel
      have hl : raw42241step0Labels = labelEmbedding6 ∘ raw42241step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42241step0 raw42241step0Labels raw42241step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw42242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42242Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42242step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42242step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42242step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42242step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42242step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42242 raw42242Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw42242 raw42242Labels = mixedMoment B raw42242step0 raw42242step0Labels := by
      have ha : raw42242step0 = (fun i j => raw42242 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42242step0 raw42242; decide +kernel
      have hl : raw42242step0Labels = raw42242Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42242 raw42242Labels permutation682 permutation2
    mixedMoment B raw42242step0 raw42242step0Labels = mixedMoment B raw42242step1 raw42242step1Labels := by
      have ha : raw42242step1 = -raw42242step0 := by apply Matrix.ext; change ∀ i j, raw42242step1 i j = -(raw42242step0 i j); unfold raw42242step1 raw42242step0; decide +kernel
      have hl : raw42242step1Labels = raw42242step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42242step1 raw42242step1Labels = mixedMoment B raw42242step2 raw42242step2Labels := by
      have ha : raw42242step2 = raw42242step1 := by apply Matrix.ext; unfold raw42242step2 raw42242step1; decide +kernel
      have hl : raw42242step1Labels = labelEmbedding1 ∘ raw42242step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42242step1 raw42242step1Labels raw42242step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

def raw42243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42243Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42243step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42243step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42243step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42243 raw42243Labels = mixedMoment B node5138 node5138Labels := by
  calc
    mixedMoment B raw42243 raw42243Labels = mixedMoment B raw42243step0 raw42243step0Labels := by
      have ha : raw42243step0 = (fun i j => raw42243 (permutation643 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42243step0 raw42243; decide +kernel
      have hl : raw42243step0Labels = raw42243Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42243 raw42243Labels permutation643 permutation7
    mixedMoment B raw42243step0 raw42243step0Labels = mixedMoment B raw42243step1 raw42243step1Labels := by
      have ha : raw42243step1 = raw42243step0 := by apply Matrix.ext; unfold raw42243step1 raw42243step0; decide +kernel
      have hl : raw42243step0Labels = labelEmbedding6 ∘ raw42243step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42243step0 raw42243step0Labels raw42243step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5138 node5138Labels := by rfl

def raw42244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42244Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42244step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42244step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42244step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42244step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42244 raw42244Labels = mixedMoment B node2718 node2718Labels := by
  calc
    mixedMoment B raw42244 raw42244Labels = mixedMoment B raw42244step0 raw42244step0Labels := by
      have ha : raw42244step0 = (fun i j => raw42244 (permutation617 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42244step0 raw42244; decide +kernel
      have hl : raw42244step0Labels = raw42244Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42244 raw42244Labels permutation617 permutation4
    mixedMoment B raw42244step0 raw42244step0Labels = mixedMoment B raw42244step1 raw42244step1Labels := by
      have ha : raw42244step1 = raw42244step0 := by apply Matrix.ext; unfold raw42244step1 raw42244step0; decide +kernel
      have hl : raw42244step0Labels = labelEmbedding1 ∘ raw42244step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42244step0 raw42244step0Labels raw42244step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2718 node2718Labels := by rfl

def raw42245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42245Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42245step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42245step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42245step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42245 raw42245Labels = mixedMoment B node5255 node5255Labels := by
  calc
    mixedMoment B raw42245 raw42245Labels = mixedMoment B raw42245step0 raw42245step0Labels := by
      have ha : raw42245step0 = (fun i j => raw42245 (permutation617 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42245step0 raw42245; decide +kernel
      have hl : raw42245step0Labels = raw42245Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42245 raw42245Labels permutation617 permutation4
    mixedMoment B raw42245step0 raw42245step0Labels = mixedMoment B raw42245step1 raw42245step1Labels := by
      have ha : raw42245step1 = raw42245step0 := by apply Matrix.ext; unfold raw42245step1 raw42245step0; decide +kernel
      have hl : raw42245step0Labels = labelEmbedding10 ∘ raw42245step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42245step0 raw42245step0Labels raw42245step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5255 node5255Labels := by rfl

def raw42246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42246Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42246step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42246step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42246step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42246 raw42246Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw42246 raw42246Labels = mixedMoment B raw42246step0 raw42246step0Labels := by
      have ha : raw42246step0 = (fun i j => raw42246 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42246step0 raw42246; decide +kernel
      have hl : raw42246step0Labels = raw42246Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42246 raw42246Labels permutation157 permutation2
    mixedMoment B raw42246step0 raw42246step0Labels = mixedMoment B raw42246step1 raw42246step1Labels := by
      have ha : raw42246step1 = raw42246step0 := by apply Matrix.ext; unfold raw42246step1 raw42246step0; decide +kernel
      have hl : raw42246step0Labels = labelEmbedding1 ∘ raw42246step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42246step0 raw42246step0Labels raw42246step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw42247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42247Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42247step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42247step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42247 raw42247Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw42247 raw42247Labels = mixedMoment B raw42247step0 raw42247step0Labels := by
      have ha : raw42247step0 = (fun i j => raw42247 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42247step0 raw42247; decide +kernel
      have hl : raw42247step0Labels = raw42247Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42247 raw42247Labels permutation157 permutation2
    mixedMoment B raw42247step0 raw42247step0Labels = mixedMoment B raw42247step1 raw42247step1Labels := by
      have ha : raw42247step1 = raw42247step0 := by apply Matrix.ext; unfold raw42247step1 raw42247step0; decide +kernel
      have hl : raw42247step0Labels = labelEmbedding8 ∘ raw42247step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42247step0 raw42247step0Labels raw42247step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5480 node5480Labels := by rfl

def raw42248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42248Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42248step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42248step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 2, -3], ![2, -3, 1]]
def raw42248step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42248step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42248step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42248step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42248step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42248 raw42248Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw42248 raw42248Labels = mixedMoment B raw42248step0 raw42248step0Labels := by
      have hz : ∀ j, raw42248 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42248step0 = (fun i j => raw42248 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42248step0 raw42248; decide +kernel
      have hl : raw42248step0Labels = raw42248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42248 raw42248Labels permutation434 hz
    mixedMoment B raw42248step0 raw42248step0Labels = mixedMoment B raw42248step1 raw42248step1Labels := by
      have hz : ∀ j, raw42248step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42248step1 = (fun i j => raw42248step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42248step1 raw42248step0; decide +kernel
      have hl : raw42248step1Labels = raw42248step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42248step0 raw42248step0Labels permutation80 hz
    mixedMoment B raw42248step1 raw42248step1Labels = mixedMoment B raw42248step2 raw42248step2Labels := by
      have ha : raw42248step2 = (fun i j => raw42248step1 (permutation28 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42248step2 raw42248step1; decide +kernel
      have hl : raw42248step2Labels = raw42248step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42248step1 raw42248step1Labels permutation28 permutation4
    mixedMoment B raw42248step2 raw42248step2Labels = mixedMoment B raw42248step3 raw42248step3Labels := by
      have ha : raw42248step3 = raw42248step2 := by apply Matrix.ext; unfold raw42248step3 raw42248step2; decide +kernel
      have hl : raw42248step2Labels = labelEmbedding1 ∘ raw42248step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42248step2 raw42248step2Labels raw42248step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw42249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42249Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![2, -3, 1]]
def raw42249step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42249step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 2, -3], ![2, -3, 1]]
def raw42249step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42249step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42249step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42249step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42249step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42249 raw42249Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw42249 raw42249Labels = mixedMoment B raw42249step0 raw42249step0Labels := by
      have hz : ∀ j, raw42249 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42249step0 = (fun i j => raw42249 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42249step0 raw42249; decide +kernel
      have hl : raw42249step0Labels = raw42249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42249 raw42249Labels permutation434 hz
    mixedMoment B raw42249step0 raw42249step0Labels = mixedMoment B raw42249step1 raw42249step1Labels := by
      have hz : ∀ j, raw42249step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42249step1 = (fun i j => raw42249step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42249step1 raw42249step0; decide +kernel
      have hl : raw42249step1Labels = raw42249step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42249step0 raw42249step0Labels permutation80 hz
    mixedMoment B raw42249step1 raw42249step1Labels = mixedMoment B raw42249step2 raw42249step2Labels := by
      have ha : raw42249step2 = (fun i j => raw42249step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42249step2 raw42249step1; decide +kernel
      have hl : raw42249step2Labels = raw42249step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42249step1 raw42249step1Labels permutation28 permutation5
    mixedMoment B raw42249step2 raw42249step2Labels = mixedMoment B raw42249step3 raw42249step3Labels := by
      have ha : raw42249step3 = raw42249step2 := by apply Matrix.ext; unfold raw42249step3 raw42249step2; decide +kernel
      have hl : raw42249step2Labels = labelEmbedding9 ∘ raw42249step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42249step2 raw42249step2Labels raw42249step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw42250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42250Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42250step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42250step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2], ![2, 2, -4]]
def raw42250step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42250step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42250step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42250step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42250step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42250 raw42250Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw42250 raw42250Labels = mixedMoment B raw42250step0 raw42250step0Labels := by
      have hz : ∀ j, raw42250 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42250step0 = (fun i j => raw42250 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42250step0 raw42250; decide +kernel
      have hl : raw42250step0Labels = raw42250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42250 raw42250Labels permutation434 hz
    mixedMoment B raw42250step0 raw42250step0Labels = mixedMoment B raw42250step1 raw42250step1Labels := by
      have hz : ∀ j, raw42250step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42250step1 = (fun i j => raw42250step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42250step1 raw42250step0; decide +kernel
      have hl : raw42250step1Labels = raw42250step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42250step0 raw42250step0Labels permutation80 hz
    mixedMoment B raw42250step1 raw42250step1Labels = mixedMoment B raw42250step2 raw42250step2Labels := by
      have ha : raw42250step2 = (fun i j => raw42250step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42250step2 raw42250step1; decide +kernel
      have hl : raw42250step2Labels = raw42250step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42250step1 raw42250step1Labels permutation22 permutation4
    mixedMoment B raw42250step2 raw42250step2Labels = mixedMoment B raw42250step3 raw42250step3Labels := by
      have ha : raw42250step3 = raw42250step2 := by apply Matrix.ext; unfold raw42250step3 raw42250step2; decide +kernel
      have hl : raw42250step2Labels = labelEmbedding1 ∘ raw42250step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42250step2 raw42250step2Labels raw42250step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2737 node2737Labels := by rfl

def raw42251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42251Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -3, 2], ![2, 2, -4]]
def raw42251step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42251step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2], ![2, 2, -4]]
def raw42251step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42251step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42251step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42251 raw42251Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw42251 raw42251Labels = mixedMoment B raw42251step0 raw42251step0Labels := by
      have hz : ∀ j, raw42251 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42251step0 = (fun i j => raw42251 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42251step0 raw42251; decide +kernel
      have hl : raw42251step0Labels = raw42251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42251 raw42251Labels permutation434 hz
    mixedMoment B raw42251step0 raw42251step0Labels = mixedMoment B raw42251step1 raw42251step1Labels := by
      have hz : ∀ j, raw42251step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42251step1 = (fun i j => raw42251step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42251step1 raw42251step0; decide +kernel
      have hl : raw42251step1Labels = raw42251step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42251step0 raw42251step0Labels permutation80 hz
    mixedMoment B raw42251step1 raw42251step1Labels = mixedMoment B raw42251step2 raw42251step2Labels := by
      have ha : raw42251step2 = (fun i j => raw42251step1 (permutation26 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42251step2 raw42251step1; decide +kernel
      have hl : raw42251step2Labels = raw42251step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42251step1 raw42251step1Labels permutation26 permutation6
    _ = mixedMoment B node4617 node4617Labels := by rfl

def raw42252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42252Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42252step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42252step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42252step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42252step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42252step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42252 raw42252Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw42252 raw42252Labels = mixedMoment B raw42252step0 raw42252step0Labels := by
      have hz : ∀ j, raw42252 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42252step0 = (fun i j => raw42252 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42252step0 raw42252; decide +kernel
      have hl : raw42252step0Labels = raw42252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42252 raw42252Labels permutation346 hz
    mixedMoment B raw42252step0 raw42252step0Labels = mixedMoment B raw42252step1 raw42252step1Labels := by
      have ha : raw42252step1 = (fun i j => raw42252step0 (permutation104 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42252step1 raw42252step0; decide +kernel
      have hl : raw42252step1Labels = raw42252step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42252step0 raw42252step0Labels permutation104 permutation4
    mixedMoment B raw42252step1 raw42252step1Labels = mixedMoment B raw42252step2 raw42252step2Labels := by
      have ha : raw42252step2 = -raw42252step1 := by apply Matrix.ext; change ∀ i j, raw42252step2 i j = -(raw42252step1 i j); unfold raw42252step2 raw42252step1; decide +kernel
      have hl : raw42252step2Labels = raw42252step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42252step2 raw42252step2Labels = mixedMoment B raw42252step3 raw42252step3Labels := by
      have ha : raw42252step3 = raw42252step2 := by apply Matrix.ext; unfold raw42252step3 raw42252step2; decide +kernel
      have hl : raw42252step2Labels = labelEmbedding1 ∘ raw42252step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42252step2 raw42252step2Labels raw42252step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw42253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42253Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw42253step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42253 raw42253Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw42253 raw42253Labels = mixedMoment B raw42253step0 raw42253step0Labels := by
      have hz : ∀ j, raw42253 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42253step0 = (fun i j => raw42253 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42253step0 raw42253; decide +kernel
      have hl : raw42253step0Labels = raw42253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42253 raw42253Labels permutation346 hz
    mixedMoment B raw42253step0 raw42253step0Labels = mixedMoment B raw42253step1 raw42253step1Labels := by
      have ha : raw42253step1 = (fun i j => raw42253step0 (permutation122 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42253step1 raw42253step0; decide +kernel
      have hl : raw42253step1Labels = raw42253step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42253step0 raw42253step0Labels permutation122 permutation6
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw42254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42254Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42254step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42254step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42254step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42254step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42254step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42254step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42254 raw42254Labels = mixedMoment B node3303 node3303Labels := by
  calc
    mixedMoment B raw42254 raw42254Labels = mixedMoment B raw42254step0 raw42254step0Labels := by
      have hz : ∀ j, raw42254 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42254step0 = (fun i j => raw42254 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42254step0 raw42254; decide +kernel
      have hl : raw42254step0Labels = raw42254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42254 raw42254Labels permutation346 hz
    mixedMoment B raw42254step0 raw42254step0Labels = mixedMoment B raw42254step1 raw42254step1Labels := by
      have ha : raw42254step1 = (fun i j => raw42254step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42254step1 raw42254step0; decide +kernel
      have hl : raw42254step1Labels = raw42254step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42254step0 raw42254step0Labels permutation151 permutation2
    mixedMoment B raw42254step1 raw42254step1Labels = mixedMoment B raw42254step2 raw42254step2Labels := by
      have ha : raw42254step2 = -raw42254step1 := by apply Matrix.ext; change ∀ i j, raw42254step2 i j = -(raw42254step1 i j); unfold raw42254step2 raw42254step1; decide +kernel
      have hl : raw42254step2Labels = raw42254step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42254step2 raw42254step2Labels = mixedMoment B raw42254step3 raw42254step3Labels := by
      have ha : raw42254step3 = raw42254step2 := by apply Matrix.ext; unfold raw42254step3 raw42254step2; decide +kernel
      have hl : raw42254step2Labels = labelEmbedding1 ∘ raw42254step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42254step2 raw42254step2Labels raw42254step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3303 node3303Labels := by rfl

def raw42255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42255Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw42255step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42255step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42255 raw42255Labels = mixedMoment B node4616 node4616Labels := by
  calc
    mixedMoment B raw42255 raw42255Labels = mixedMoment B raw42255step0 raw42255step0Labels := by
      have hz : ∀ j, raw42255 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42255step0 = (fun i j => raw42255 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42255step0 raw42255; decide +kernel
      have hl : raw42255step0Labels = raw42255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42255 raw42255Labels permutation346 hz
    mixedMoment B raw42255step0 raw42255step0Labels = mixedMoment B raw42255step1 raw42255step1Labels := by
      have ha : raw42255step1 = (fun i j => raw42255step0 (permutation128 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42255step1 raw42255step0; decide +kernel
      have hl : raw42255step1Labels = raw42255step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42255step0 raw42255step0Labels permutation128 permutation6
    _ = mixedMoment B node4616 node4616Labels := by rfl

def raw42256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42256Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42256step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42256step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42256step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42256step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42256step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42256 raw42256Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw42256 raw42256Labels = mixedMoment B raw42256step0 raw42256step0Labels := by
      have hz : ∀ j, raw42256 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42256step0 = (fun i j => raw42256 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42256step0 raw42256; decide +kernel
      have hl : raw42256step0Labels = raw42256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42256 raw42256Labels permutation346 hz
    mixedMoment B raw42256step0 raw42256step0Labels = mixedMoment B raw42256step1 raw42256step1Labels := by
      have ha : raw42256step1 = (fun i j => raw42256step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42256step1 raw42256step0; decide +kernel
      have hl : raw42256step1Labels = raw42256step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42256step0 raw42256step0Labels permutation151 permutation2
    mixedMoment B raw42256step1 raw42256step1Labels = mixedMoment B raw42256step2 raw42256step2Labels := by
      have ha : raw42256step2 = -raw42256step1 := by apply Matrix.ext; change ∀ i j, raw42256step2 i j = -(raw42256step1 i j); unfold raw42256step2 raw42256step1; decide +kernel
      have hl : raw42256step2Labels = raw42256step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42256step2 raw42256step2Labels = mixedMoment B raw42256step3 raw42256step3Labels := by
      have ha : raw42256step3 = raw42256step2 := by apply Matrix.ext; unfold raw42256step3 raw42256step2; decide +kernel
      have hl : raw42256step2Labels = labelEmbedding1 ∘ raw42256step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42256step2 raw42256step2Labels raw42256step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

def raw42257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42257Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw42257step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42257step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42257step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42257step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42257 raw42257Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw42257 raw42257Labels = mixedMoment B raw42257step0 raw42257step0Labels := by
      have hz : ∀ j, raw42257 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42257step0 = (fun i j => raw42257 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42257step0 raw42257; decide +kernel
      have hl : raw42257step0Labels = raw42257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42257 raw42257Labels permutation346 hz
    mixedMoment B raw42257step0 raw42257step0Labels = mixedMoment B raw42257step1 raw42257step1Labels := by
      have ha : raw42257step1 = (fun i j => raw42257step0 (permutation148 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42257step1 raw42257step0; decide +kernel
      have hl : raw42257step1Labels = raw42257step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42257step0 raw42257step0Labels permutation148 permutation7
    mixedMoment B raw42257step1 raw42257step1Labels = mixedMoment B raw42257step2 raw42257step2Labels := by
      have ha : raw42257step2 = raw42257step1 := by apply Matrix.ext; unfold raw42257step2 raw42257step1; decide +kernel
      have hl : raw42257step1Labels = labelEmbedding6 ∘ raw42257step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42257step1 raw42257step1Labels raw42257step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4607 node4607Labels := by rfl

def raw42258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw42258Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw42258step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42258step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42258 raw42258Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw42258 raw42258Labels = mixedMoment B raw42258step0 raw42258step0Labels := by
      have hz : ∀ j, raw42258 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42258step0 = (fun i j => raw42258 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42258step0 raw42258; decide +kernel
      have hl : raw42258step0Labels = raw42258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42258 raw42258Labels permutation346 hz
    mixedMoment B raw42258step0 raw42258step0Labels = mixedMoment B raw42258step1 raw42258step1Labels := by
      have ha : raw42258step1 = (fun i j => raw42258step0 (permutation138 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42258step1 raw42258step0; decide +kernel
      have hl : raw42258step1Labels = raw42258step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42258step0 raw42258step0Labels permutation138 permutation4
    mixedMoment B raw42258step1 raw42258step1Labels = mixedMoment B raw42258step2 raw42258step2Labels := by
      have ha : raw42258step2 = raw42258step1 := by apply Matrix.ext; unfold raw42258step2 raw42258step1; decide +kernel
      have hl : raw42258step1Labels = labelEmbedding1 ∘ raw42258step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42258step1 raw42258step1Labels raw42258step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2719 node2719Labels := by rfl

def raw42259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw42259Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 2, -3], ![1, 0, -1], ![1, -3, 2]]
def raw42259step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42259 raw42259Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw42259 raw42259Labels = mixedMoment B raw42259step0 raw42259step0Labels := by
      have hz : ∀ j, raw42259 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42259step0 = (fun i j => raw42259 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42259step0 raw42259; decide +kernel
      have hl : raw42259step0Labels = raw42259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42259 raw42259Labels permutation346 hz
    mixedMoment B raw42259step0 raw42259step0Labels = mixedMoment B raw42259step1 raw42259step1Labels := by
      have ha : raw42259step1 = (fun i j => raw42259step0 (permutation92 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42259step1 raw42259step0; decide +kernel
      have hl : raw42259step1Labels = raw42259step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42259step0 raw42259step0Labels permutation92 permutation6
    _ = mixedMoment B node5161 node5161Labels := by rfl

def raw42260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw42260Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw42260step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw42260step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42260step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42260step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42260step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42260step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42260 raw42260Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw42260 raw42260Labels = mixedMoment B raw42260step0 raw42260step0Labels := by
      have hz : ∀ j, raw42260 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42260step0 = (fun i j => raw42260 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42260step0 raw42260; decide +kernel
      have hl : raw42260step0Labels = raw42260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42260 raw42260Labels permutation346 hz
    mixedMoment B raw42260step0 raw42260step0Labels = mixedMoment B raw42260step1 raw42260step1Labels := by
      have ha : raw42260step1 = (fun i j => raw42260step0 (permutation80 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42260step1 raw42260step0; decide +kernel
      have hl : raw42260step1Labels = raw42260step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42260step0 raw42260step0Labels permutation80 permutation4
    mixedMoment B raw42260step1 raw42260step1Labels = mixedMoment B raw42260step2 raw42260step2Labels := by
      have ha : raw42260step2 = -raw42260step1 := by apply Matrix.ext; change ∀ i j, raw42260step2 i j = -(raw42260step1 i j); unfold raw42260step2 raw42260step1; decide +kernel
      have hl : raw42260step2Labels = raw42260step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42260step2 raw42260step2Labels = mixedMoment B raw42260step3 raw42260step3Labels := by
      have ha : raw42260step3 = raw42260step2 := by apply Matrix.ext; unfold raw42260step3 raw42260step2; decide +kernel
      have hl : raw42260step2Labels = labelEmbedding1 ∘ raw42260step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42260step2 raw42260step2Labels raw42260step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw42261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw42261Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 2, -3], ![1, -1, 0], ![1, -2, 1]]
def raw42261step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42261step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42261 raw42261Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw42261 raw42261Labels = mixedMoment B raw42261step0 raw42261step0Labels := by
      have hz : ∀ j, raw42261 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42261step0 = (fun i j => raw42261 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42261step0 raw42261; decide +kernel
      have hl : raw42261step0Labels = raw42261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42261 raw42261Labels permutation346 hz
    mixedMoment B raw42261step0 raw42261step0Labels = mixedMoment B raw42261step1 raw42261step1Labels := by
      have ha : raw42261step1 = (fun i j => raw42261step0 (permutation92 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42261step1 raw42261step0; decide +kernel
      have hl : raw42261step1Labels = raw42261step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42261step0 raw42261step0Labels permutation92 permutation6
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw42262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw42262Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw42262step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42262step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42262step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42262 raw42262Labels = mixedMoment B node2736 node2736Labels := by
  calc
    mixedMoment B raw42262 raw42262Labels = mixedMoment B raw42262step0 raw42262step0Labels := by
      have hz : ∀ j, raw42262 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42262step0 = (fun i j => raw42262 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42262step0 raw42262; decide +kernel
      have hl : raw42262step0Labels = raw42262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42262 raw42262Labels permutation346 hz
    mixedMoment B raw42262step0 raw42262step0Labels = mixedMoment B raw42262step1 raw42262step1Labels := by
      have ha : raw42262step1 = (fun i j => raw42262step0 (permutation134 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42262step1 raw42262step0; decide +kernel
      have hl : raw42262step1Labels = raw42262step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42262step0 raw42262step0Labels permutation134 permutation4
    mixedMoment B raw42262step1 raw42262step1Labels = mixedMoment B raw42262step2 raw42262step2Labels := by
      have ha : raw42262step2 = raw42262step1 := by apply Matrix.ext; unfold raw42262step2 raw42262step1; decide +kernel
      have hl : raw42262step1Labels = labelEmbedding1 ∘ raw42262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42262step1 raw42262step1Labels raw42262step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2736 node2736Labels := by rfl

def raw42263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw42263Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![1, -3, 2]]
def raw42263step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42263step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42263step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42263step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42263 raw42263Labels = mixedMoment B node5269 node5269Labels := by
  calc
    mixedMoment B raw42263 raw42263Labels = mixedMoment B raw42263step0 raw42263step0Labels := by
      have hz : ∀ j, raw42263 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42263step0 = (fun i j => raw42263 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42263step0 raw42263; decide +kernel
      have hl : raw42263step0Labels = raw42263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42263 raw42263Labels permutation346 hz
    mixedMoment B raw42263step0 raw42263step0Labels = mixedMoment B raw42263step1 raw42263step1Labels := by
      have ha : raw42263step1 = (fun i j => raw42263step0 (permutation134 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42263step1 raw42263step0; decide +kernel
      have hl : raw42263step1Labels = raw42263step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42263step0 raw42263step0Labels permutation134 permutation4
    mixedMoment B raw42263step1 raw42263step1Labels = mixedMoment B raw42263step2 raw42263step2Labels := by
      have ha : raw42263step2 = raw42263step1 := by apply Matrix.ext; unfold raw42263step2 raw42263step1; decide +kernel
      have hl : raw42263step1Labels = labelEmbedding10 ∘ raw42263step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42263step1 raw42263step1Labels raw42263step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5269 node5269Labels := by rfl

def raw42264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42264Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42264step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42264step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42264step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42264step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42264 raw42264Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw42264 raw42264Labels = mixedMoment B raw42264step0 raw42264step0Labels := by
      have ha : raw42264step0 = (fun i j => raw42264 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42264step0 raw42264; decide +kernel
      have hl : raw42264step0Labels = raw42264Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42264 raw42264Labels permutation682 permutation2
    mixedMoment B raw42264step0 raw42264step0Labels = mixedMoment B raw42264step1 raw42264step1Labels := by
      have ha : raw42264step1 = -raw42264step0 := by apply Matrix.ext; change ∀ i j, raw42264step1 i j = -(raw42264step0 i j); unfold raw42264step1 raw42264step0; decide +kernel
      have hl : raw42264step1Labels = raw42264step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42264step1 raw42264step1Labels = mixedMoment B raw42264step2 raw42264step2Labels := by
      have ha : raw42264step2 = raw42264step1 := by apply Matrix.ext; unfold raw42264step2 raw42264step1; decide +kernel
      have hl : raw42264step1Labels = labelEmbedding1 ∘ raw42264step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42264step1 raw42264step1Labels raw42264step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

def raw42265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42265Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42265step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42265step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42265 raw42265Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw42265 raw42265Labels = mixedMoment B raw42265step0 raw42265step0Labels := by
      have ha : raw42265step0 = (fun i j => raw42265 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42265step0 raw42265; decide +kernel
      have hl : raw42265step0Labels = raw42265Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42265 raw42265Labels permutation682 permutation7
    mixedMoment B raw42265step0 raw42265step0Labels = mixedMoment B raw42265step1 raw42265step1Labels := by
      have ha : raw42265step1 = raw42265step0 := by apply Matrix.ext; unfold raw42265step1 raw42265step0; decide +kernel
      have hl : raw42265step0Labels = labelEmbedding6 ∘ raw42265step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42265step0 raw42265step0Labels raw42265step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw42266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42266Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42266step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42266step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42266step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42266step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42266step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42266 raw42266Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw42266 raw42266Labels = mixedMoment B raw42266step0 raw42266step0Labels := by
      have ha : raw42266step0 = (fun i j => raw42266 (permutation443 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42266step0 raw42266; decide +kernel
      have hl : raw42266step0Labels = raw42266Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42266 raw42266Labels permutation443 permutation4
    mixedMoment B raw42266step0 raw42266step0Labels = mixedMoment B raw42266step1 raw42266step1Labels := by
      have ha : raw42266step1 = -raw42266step0 := by apply Matrix.ext; change ∀ i j, raw42266step1 i j = -(raw42266step0 i j); unfold raw42266step1 raw42266step0; decide +kernel
      have hl : raw42266step1Labels = raw42266step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42266step1 raw42266step1Labels = mixedMoment B raw42266step2 raw42266step2Labels := by
      have ha : raw42266step2 = raw42266step1 := by apply Matrix.ext; unfold raw42266step2 raw42266step1; decide +kernel
      have hl : raw42266step1Labels = labelEmbedding1 ∘ raw42266step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42266step1 raw42266step1Labels raw42266step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

def raw42267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42267Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42267step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42267 raw42267Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw42267 raw42267Labels = mixedMoment B raw42267step0 raw42267step0Labels := by
      have ha : raw42267step0 = (fun i j => raw42267 (permutation484 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42267step0 raw42267; decide +kernel
      have hl : raw42267step0Labels = raw42267Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42267 raw42267Labels permutation484 permutation6
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw42268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42268Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42268step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42268step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42268step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42268step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42268step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42268 raw42268Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw42268 raw42268Labels = mixedMoment B raw42268step0 raw42268step0Labels := by
      have ha : raw42268step0 = (fun i j => raw42268 (permutation437 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42268step0 raw42268; decide +kernel
      have hl : raw42268step0Labels = raw42268Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42268 raw42268Labels permutation437 permutation4
    mixedMoment B raw42268step0 raw42268step0Labels = mixedMoment B raw42268step1 raw42268step1Labels := by
      have ha : raw42268step1 = -raw42268step0 := by apply Matrix.ext; change ∀ i j, raw42268step1 i j = -(raw42268step0 i j); unfold raw42268step1 raw42268step0; decide +kernel
      have hl : raw42268step1Labels = raw42268step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42268step1 raw42268step1Labels = mixedMoment B raw42268step2 raw42268step2Labels := by
      have ha : raw42268step2 = raw42268step1 := by apply Matrix.ext; unfold raw42268step2 raw42268step1; decide +kernel
      have hl : raw42268step1Labels = labelEmbedding1 ∘ raw42268step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42268step1 raw42268step1Labels raw42268step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3571 node3571Labels := by rfl

def raw42269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42269Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42269 raw42269Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw42269 raw42269Labels = mixedMoment B raw42269step0 raw42269step0Labels := by
      have ha : raw42269step0 = (fun i j => raw42269 (permutation499 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42269step0 raw42269; decide +kernel
      have hl : raw42269step0Labels = raw42269Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42269 raw42269Labels permutation499 permutation6
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw42270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42270Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42270step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42270step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42270step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42270 raw42270Labels = mixedMoment B node3973 node3973Labels := by
  calc
    mixedMoment B raw42270 raw42270Labels = mixedMoment B raw42270step0 raw42270step0Labels := by
      have ha : raw42270step0 = (fun i j => raw42270 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42270step0 raw42270; decide +kernel
      have hl : raw42270step0Labels = raw42270Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42270 raw42270Labels permutation156 permutation2
    mixedMoment B raw42270step0 raw42270step0Labels = mixedMoment B raw42270step1 raw42270step1Labels := by
      have ha : raw42270step1 = raw42270step0 := by apply Matrix.ext; unfold raw42270step1 raw42270step0; decide +kernel
      have hl : raw42270step0Labels = labelEmbedding1 ∘ raw42270step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42270step0 raw42270step0Labels raw42270step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3973 node3973Labels := by rfl

def raw42271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42271Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42271 raw42271Labels = mixedMoment B node5461 node5461Labels := by
  calc
    mixedMoment B raw42271 raw42271Labels = mixedMoment B raw42271step0 raw42271step0Labels := by
      have ha : raw42271step0 = (fun i j => raw42271 (permutation484 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42271step0 raw42271; decide +kernel
      have hl : raw42271step0Labels = raw42271Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42271 raw42271Labels permutation484 permutation6
    _ = mixedMoment B node5461 node5461Labels := by rfl

def raw42272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42272Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42272step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw42272step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42272step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42272step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42272step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42272step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42272 raw42272Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw42272 raw42272Labels = mixedMoment B raw42272step0 raw42272step0Labels := by
      have ha : raw42272step0 = (fun i j => raw42272 (permutation444 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42272step0 raw42272; decide +kernel
      have hl : raw42272step0Labels = raw42272Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42272 raw42272Labels permutation444 permutation4
    mixedMoment B raw42272step0 raw42272step0Labels = mixedMoment B raw42272step1 raw42272step1Labels := by
      have ha : raw42272step1 = -raw42272step0 := by apply Matrix.ext; change ∀ i j, raw42272step1 i j = -(raw42272step0 i j); unfold raw42272step1 raw42272step0; decide +kernel
      have hl : raw42272step1Labels = raw42272step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42272step1 raw42272step1Labels = mixedMoment B raw42272step2 raw42272step2Labels := by
      have ha : raw42272step2 = raw42272step1 := by apply Matrix.ext; unfold raw42272step2 raw42272step1; decide +kernel
      have hl : raw42272step1Labels = labelEmbedding1 ∘ raw42272step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42272step1 raw42272step1Labels raw42272step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

def raw42273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42273Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42273step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42273 raw42273Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw42273 raw42273Labels = mixedMoment B raw42273step0 raw42273step0Labels := by
      have ha : raw42273step0 = (fun i j => raw42273 (permutation499 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42273step0 raw42273; decide +kernel
      have hl : raw42273step0Labels = raw42273Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42273 raw42273Labels permutation499 permutation6
    _ = mixedMoment B node5144 node5144Labels := by rfl

def raw42274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42274Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42274step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42274step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42274 raw42274Labels = mixedMoment B node3842 node3842Labels := by
  calc
    mixedMoment B raw42274 raw42274Labels = mixedMoment B raw42274step0 raw42274step0Labels := by
      have ha : raw42274step0 = (fun i j => raw42274 (permutation419 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42274step0 raw42274; decide +kernel
      have hl : raw42274step0Labels = raw42274Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42274 raw42274Labels permutation419 permutation4
    mixedMoment B raw42274step0 raw42274step0Labels = mixedMoment B raw42274step1 raw42274step1Labels := by
      have ha : raw42274step1 = raw42274step0 := by apply Matrix.ext; unfold raw42274step1 raw42274step0; decide +kernel
      have hl : raw42274step0Labels = labelEmbedding1 ∘ raw42274step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42274step0 raw42274step0Labels raw42274step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3842 node3842Labels := by rfl

def raw42275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42275Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw42275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42275step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw42275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42275 raw42275Labels = mixedMoment B node5419 node5419Labels := by
  calc
    mixedMoment B raw42275 raw42275Labels = mixedMoment B raw42275step0 raw42275step0Labels := by
      have ha : raw42275step0 = (fun i j => raw42275 (permutation370 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42275step0 raw42275; decide +kernel
      have hl : raw42275step0Labels = raw42275Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42275 raw42275Labels permutation370 permutation6
    mixedMoment B raw42275step0 raw42275step0Labels = mixedMoment B raw42275step1 raw42275step1Labels := by
      have ha : raw42275step1 = -raw42275step0 := by apply Matrix.ext; change ∀ i j, raw42275step1 i j = -(raw42275step0 i j); unfold raw42275step1 raw42275step0; decide +kernel
      have hl : raw42275step1Labels = raw42275step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5419 node5419Labels := by rfl

def raw42276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42276Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42276step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42276step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42276step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42276step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42276step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42276 raw42276Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw42276 raw42276Labels = mixedMoment B raw42276step0 raw42276step0Labels := by
      have hz : ∀ j, raw42276 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42276step0 = (fun i j => raw42276 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42276step0 raw42276; decide +kernel
      have hl : raw42276step0Labels = raw42276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42276 raw42276Labels permutation434 hz
    mixedMoment B raw42276step0 raw42276step0Labels = mixedMoment B raw42276step1 raw42276step1Labels := by
      have ha : raw42276step1 = (fun i j => raw42276step0 (permutation82 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42276step1 raw42276step0; decide +kernel
      have hl : raw42276step1Labels = raw42276step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42276step0 raw42276step0Labels permutation82 permutation4
    mixedMoment B raw42276step1 raw42276step1Labels = mixedMoment B raw42276step2 raw42276step2Labels := by
      have ha : raw42276step2 = -raw42276step1 := by apply Matrix.ext; change ∀ i j, raw42276step2 i j = -(raw42276step1 i j); unfold raw42276step2 raw42276step1; decide +kernel
      have hl : raw42276step2Labels = raw42276step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42276step2 raw42276step2Labels = mixedMoment B raw42276step3 raw42276step3Labels := by
      have ha : raw42276step3 = raw42276step2 := by apply Matrix.ext; unfold raw42276step3 raw42276step2; decide +kernel
      have hl : raw42276step2Labels = labelEmbedding1 ∘ raw42276step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42276step2 raw42276step2Labels raw42276step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw42277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw42277Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42277step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw42277step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42277step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42277step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42277step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42277 raw42277Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw42277 raw42277Labels = mixedMoment B raw42277step0 raw42277step0Labels := by
      have hz : ∀ j, raw42277 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42277step0 = (fun i j => raw42277 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42277step0 raw42277; decide +kernel
      have hl : raw42277step0Labels = raw42277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42277 raw42277Labels permutation434 hz
    mixedMoment B raw42277step0 raw42277step0Labels = mixedMoment B raw42277step1 raw42277step1Labels := by
      have ha : raw42277step1 = (fun i j => raw42277step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42277step1 raw42277step0; decide +kernel
      have hl : raw42277step1Labels = raw42277step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42277step0 raw42277step0Labels permutation151 permutation3
    mixedMoment B raw42277step1 raw42277step1Labels = mixedMoment B raw42277step2 raw42277step2Labels := by
      have ha : raw42277step2 = -raw42277step1 := by apply Matrix.ext; change ∀ i j, raw42277step2 i j = -(raw42277step1 i j); unfold raw42277step2 raw42277step1; decide +kernel
      have hl : raw42277step2Labels = raw42277step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42277step2 raw42277step2Labels = mixedMoment B raw42277step3 raw42277step3Labels := by
      have ha : raw42277step3 = raw42277step2 := by apply Matrix.ext; unfold raw42277step3 raw42277step2; decide +kernel
      have hl : raw42277step2Labels = labelEmbedding7 ∘ raw42277step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42277step2 raw42277step2Labels raw42277step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

def raw42278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42278Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42278step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42278step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw42278step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42278step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42278step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42278step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42278step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42278 raw42278Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw42278 raw42278Labels = mixedMoment B raw42278step0 raw42278step0Labels := by
      have hz : ∀ j, raw42278 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42278step0 = (fun i j => raw42278 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42278step0 raw42278; decide +kernel
      have hl : raw42278step0Labels = raw42278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42278 raw42278Labels permutation434 hz
    mixedMoment B raw42278step0 raw42278step0Labels = mixedMoment B raw42278step1 raw42278step1Labels := by
      have ha : raw42278step1 = (fun i j => raw42278step0 (permutation85 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42278step1 raw42278step0; decide +kernel
      have hl : raw42278step1Labels = raw42278step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42278step0 raw42278step0Labels permutation85 permutation4
    mixedMoment B raw42278step1 raw42278step1Labels = mixedMoment B raw42278step2 raw42278step2Labels := by
      have ha : raw42278step2 = -raw42278step1 := by apply Matrix.ext; change ∀ i j, raw42278step2 i j = -(raw42278step1 i j); unfold raw42278step2 raw42278step1; decide +kernel
      have hl : raw42278step2Labels = raw42278step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42278step2 raw42278step2Labels = mixedMoment B raw42278step3 raw42278step3Labels := by
      have ha : raw42278step3 = raw42278step2 := by apply Matrix.ext; unfold raw42278step3 raw42278step2; decide +kernel
      have hl : raw42278step2Labels = labelEmbedding1 ∘ raw42278step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42278step2 raw42278step2Labels raw42278step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw42279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw42279Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42279step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42279step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42279 raw42279Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw42279 raw42279Labels = mixedMoment B raw42279step0 raw42279step0Labels := by
      have hz : ∀ j, raw42279 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42279step0 = (fun i j => raw42279 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42279step0 raw42279; decide +kernel
      have hl : raw42279step0Labels = raw42279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42279 raw42279Labels permutation434 hz
    mixedMoment B raw42279step0 raw42279step0Labels = mixedMoment B raw42279step1 raw42279step1Labels := by
      have ha : raw42279step1 = (fun i j => raw42279step0 (permutation102 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42279step1 raw42279step0; decide +kernel
      have hl : raw42279step1Labels = raw42279step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42279step0 raw42279step0Labels permutation102 permutation6
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw42280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42280Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42280step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 1, 1]]
def raw42280step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw42280step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42280step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw42280step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42280 raw42280Labels = mixedMoment B node3868 node3868Labels := by
  calc
    mixedMoment B raw42280 raw42280Labels = mixedMoment B raw42280step0 raw42280step0Labels := by
      have hz : ∀ j, raw42280 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42280step0 = (fun i j => raw42280 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42280step0 raw42280; decide +kernel
      have hl : raw42280step0Labels = raw42280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42280 raw42280Labels permutation434 hz
    mixedMoment B raw42280step0 raw42280step0Labels = mixedMoment B raw42280step1 raw42280step1Labels := by
      have ha : raw42280step1 = (fun i j => raw42280step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42280step1 raw42280step0; decide +kernel
      have hl : raw42280step1Labels = raw42280step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42280step0 raw42280step0Labels permutation151 permutation2
    mixedMoment B raw42280step1 raw42280step1Labels = mixedMoment B raw42280step2 raw42280step2Labels := by
      have ha : raw42280step2 = -raw42280step1 := by apply Matrix.ext; change ∀ i j, raw42280step2 i j = -(raw42280step1 i j); unfold raw42280step2 raw42280step1; decide +kernel
      have hl : raw42280step2Labels = raw42280step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42280step2 raw42280step2Labels = mixedMoment B raw42280step3 raw42280step3Labels := by
      have ha : raw42280step3 = raw42280step2 := by apply Matrix.ext; unfold raw42280step3 raw42280step2; decide +kernel
      have hl : raw42280step2Labels = labelEmbedding1 ∘ raw42280step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42280step2 raw42280step2Labels raw42280step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3868 node3868Labels := by rfl

def raw42281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw42281Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42281step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42281 raw42281Labels = mixedMoment B node5385 node5385Labels := by
  calc
    mixedMoment B raw42281 raw42281Labels = mixedMoment B raw42281step0 raw42281step0Labels := by
      have hz : ∀ j, raw42281 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42281step0 = (fun i j => raw42281 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42281step0 raw42281; decide +kernel
      have hl : raw42281step0Labels = raw42281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42281 raw42281Labels permutation434 hz
    mixedMoment B raw42281step0 raw42281step0Labels = mixedMoment B raw42281step1 raw42281step1Labels := by
      have ha : raw42281step1 = (fun i j => raw42281step0 (permutation99 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42281step1 raw42281step0; decide +kernel
      have hl : raw42281step1Labels = raw42281step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42281step0 raw42281step0Labels permutation99 permutation6
    _ = mixedMoment B node5385 node5385Labels := by rfl

def raw42282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42282Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw42282step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42282step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42282step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42282step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42282step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42282 raw42282Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw42282 raw42282Labels = mixedMoment B raw42282step0 raw42282step0Labels := by
      have ha : raw42282step0 = (fun i j => raw42282 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42282step0 raw42282; decide +kernel
      have hl : raw42282step0Labels = raw42282Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42282 raw42282Labels permutation682 permutation2
    mixedMoment B raw42282step0 raw42282step0Labels = mixedMoment B raw42282step1 raw42282step1Labels := by
      have ha : raw42282step1 = -raw42282step0 := by apply Matrix.ext; change ∀ i j, raw42282step1 i j = -(raw42282step0 i j); unfold raw42282step1 raw42282step0; decide +kernel
      have hl : raw42282step1Labels = raw42282step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42282step1 raw42282step1Labels = mixedMoment B raw42282step2 raw42282step2Labels := by
      have ha : raw42282step2 = raw42282step1 := by apply Matrix.ext; unfold raw42282step2 raw42282step1; decide +kernel
      have hl : raw42282step1Labels = labelEmbedding1 ∘ raw42282step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42282step1 raw42282step1Labels raw42282step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw42283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42283Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42283step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw42283step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42283step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw42283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42283 raw42283Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw42283 raw42283Labels = mixedMoment B raw42283step0 raw42283step0Labels := by
      have ha : raw42283step0 = (fun i j => raw42283 (permutation645 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42283step0 raw42283; decide +kernel
      have hl : raw42283step0Labels = raw42283Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42283 raw42283Labels permutation645 permutation7
    mixedMoment B raw42283step0 raw42283step0Labels = mixedMoment B raw42283step1 raw42283step1Labels := by
      have ha : raw42283step1 = raw42283step0 := by apply Matrix.ext; unfold raw42283step1 raw42283step0; decide +kernel
      have hl : raw42283step0Labels = labelEmbedding6 ∘ raw42283step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42283step0 raw42283step0Labels raw42283step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw42284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42284Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw42284step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42284step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42284step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42284step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42284 raw42284Labels = mixedMoment B node3869 node3869Labels := by
  calc
    mixedMoment B raw42284 raw42284Labels = mixedMoment B raw42284step0 raw42284step0Labels := by
      have ha : raw42284step0 = (fun i j => raw42284 (permutation354 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42284step0 raw42284; decide +kernel
      have hl : raw42284step0Labels = raw42284Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42284 raw42284Labels permutation354 permutation4
    mixedMoment B raw42284step0 raw42284step0Labels = mixedMoment B raw42284step1 raw42284step1Labels := by
      have ha : raw42284step1 = -raw42284step0 := by apply Matrix.ext; change ∀ i j, raw42284step1 i j = -(raw42284step0 i j); unfold raw42284step1 raw42284step0; decide +kernel
      have hl : raw42284step1Labels = raw42284step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42284step1 raw42284step1Labels = mixedMoment B raw42284step2 raw42284step2Labels := by
      have ha : raw42284step2 = raw42284step1 := by apply Matrix.ext; unfold raw42284step2 raw42284step1; decide +kernel
      have hl : raw42284step1Labels = labelEmbedding1 ∘ raw42284step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42284step1 raw42284step1Labels raw42284step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3869 node3869Labels := by rfl

def raw42285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42285Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42285 raw42285Labels = mixedMoment B node5414 node5414Labels := by
  calc
    mixedMoment B raw42285 raw42285Labels = mixedMoment B raw42285step0 raw42285step0Labels := by
      have ha : raw42285step0 = (fun i j => raw42285 (permutation390 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42285step0 raw42285; decide +kernel
      have hl : raw42285step0Labels = raw42285Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42285 raw42285Labels permutation390 permutation6
    _ = mixedMoment B node5414 node5414Labels := by rfl

def raw42286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42286Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw42286step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42286step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42286step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42286step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42286 raw42286Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw42286 raw42286Labels = mixedMoment B raw42286step0 raw42286step0Labels := by
      have ha : raw42286step0 = (fun i j => raw42286 (permutation355 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42286step0 raw42286; decide +kernel
      have hl : raw42286step0Labels = raw42286Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42286 raw42286Labels permutation355 permutation4
    mixedMoment B raw42286step0 raw42286step0Labels = mixedMoment B raw42286step1 raw42286step1Labels := by
      have ha : raw42286step1 = -raw42286step0 := by apply Matrix.ext; change ∀ i j, raw42286step1 i j = -(raw42286step0 i j); unfold raw42286step1 raw42286step0; decide +kernel
      have hl : raw42286step1Labels = raw42286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42286step1 raw42286step1Labels = mixedMoment B raw42286step2 raw42286step2Labels := by
      have ha : raw42286step2 = raw42286step1 := by apply Matrix.ext; unfold raw42286step2 raw42286step1; decide +kernel
      have hl : raw42286step1Labels = labelEmbedding1 ∘ raw42286step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42286step1 raw42286step1Labels raw42286step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3874 node3874Labels := by rfl

def raw42287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42287Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42287step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42287 raw42287Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw42287 raw42287Labels = mixedMoment B raw42287step0 raw42287step0Labels := by
      have ha : raw42287step0 = (fun i j => raw42287 (permutation393 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42287step0 raw42287; decide +kernel
      have hl : raw42287step0Labels = raw42287Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42287 raw42287Labels permutation393 permutation6
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw42288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42288Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42288step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42288 raw42288Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw42288 raw42288Labels = mixedMoment B raw42288step0 raw42288step0Labels := by
      have ha : raw42288step0 = raw42288 := by apply Matrix.ext; unfold raw42288step0 raw42288; decide +kernel
      have hl : raw42288Labels = labelEmbedding1 ∘ raw42288step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42288 raw42288Labels raw42288step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3954 node3954Labels := by rfl

def raw42289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42289Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42289step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42289step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42289step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42289step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42289 raw42289Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw42289 raw42289Labels = mixedMoment B raw42289step0 raw42289step0Labels := by
      have ha : raw42289step0 = (fun i j => raw42289 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42289step0 raw42289; decide +kernel
      have hl : raw42289step0Labels = raw42289Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42289 raw42289Labels permutation682 permutation3
    mixedMoment B raw42289step0 raw42289step0Labels = mixedMoment B raw42289step1 raw42289step1Labels := by
      have ha : raw42289step1 = -raw42289step0 := by apply Matrix.ext; change ∀ i j, raw42289step1 i j = -(raw42289step0 i j); unfold raw42289step1 raw42289step0; decide +kernel
      have hl : raw42289step1Labels = raw42289step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42289step1 raw42289step1Labels = mixedMoment B raw42289step2 raw42289step2Labels := by
      have ha : raw42289step2 = raw42289step1 := by apply Matrix.ext; unfold raw42289step2 raw42289step1; decide +kernel
      have hl : raw42289step1Labels = labelEmbedding7 ∘ raw42289step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42289step1 raw42289step1Labels raw42289step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw42290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42290Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw42290step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42290step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42290step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42290step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42290step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42290 raw42290Labels = mixedMoment B node3869 node3869Labels := by
  calc
    mixedMoment B raw42290 raw42290Labels = mixedMoment B raw42290step0 raw42290step0Labels := by
      have ha : raw42290step0 = (fun i j => raw42290 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42290step0 raw42290; decide +kernel
      have hl : raw42290step0Labels = raw42290Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42290 raw42290Labels permutation682 permutation2
    mixedMoment B raw42290step0 raw42290step0Labels = mixedMoment B raw42290step1 raw42290step1Labels := by
      have ha : raw42290step1 = -raw42290step0 := by apply Matrix.ext; change ∀ i j, raw42290step1 i j = -(raw42290step0 i j); unfold raw42290step1 raw42290step0; decide +kernel
      have hl : raw42290step1Labels = raw42290step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42290step1 raw42290step1Labels = mixedMoment B raw42290step2 raw42290step2Labels := by
      have ha : raw42290step2 = raw42290step1 := by apply Matrix.ext; unfold raw42290step2 raw42290step1; decide +kernel
      have hl : raw42290step1Labels = labelEmbedding1 ∘ raw42290step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42290step1 raw42290step1Labels raw42290step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3869 node3869Labels := by rfl

def raw42291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42291Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42291step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42291step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42291step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42291 raw42291Labels = mixedMoment B node5414 node5414Labels := by
  calc
    mixedMoment B raw42291 raw42291Labels = mixedMoment B raw42291step0 raw42291step0Labels := by
      have ha : raw42291step0 = (fun i j => raw42291 (permutation639 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42291step0 raw42291; decide +kernel
      have hl : raw42291step0Labels = raw42291Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42291 raw42291Labels permutation639 permutation7
    mixedMoment B raw42291step0 raw42291step0Labels = mixedMoment B raw42291step1 raw42291step1Labels := by
      have ha : raw42291step1 = raw42291step0 := by apply Matrix.ext; unfold raw42291step1 raw42291step0; decide +kernel
      have hl : raw42291step0Labels = labelEmbedding6 ∘ raw42291step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42291step0 raw42291step0Labels raw42291step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5414 node5414Labels := by rfl

def raw42292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42292Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42292step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42292step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42292 raw42292Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw42292 raw42292Labels = mixedMoment B raw42292step0 raw42292step0Labels := by
      have hz : ∀ j, raw42292 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42292step0 = (fun i j => raw42292 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42292step0 raw42292; decide +kernel
      have hl : raw42292step0Labels = raw42292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42292 raw42292Labels permutation434 hz
    mixedMoment B raw42292step0 raw42292step0Labels = mixedMoment B raw42292step1 raw42292step1Labels := by
      have ha : raw42292step1 = raw42292step0 := by apply Matrix.ext; unfold raw42292step1 raw42292step0; decide +kernel
      have hl : raw42292step0Labels = labelEmbedding1 ∘ raw42292step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42292step0 raw42292step0Labels raw42292step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw42293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw42293Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42293step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42293step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42293step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42293step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42293step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42293 raw42293Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw42293 raw42293Labels = mixedMoment B raw42293step0 raw42293step0Labels := by
      have hz : ∀ j, raw42293 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42293step0 = (fun i j => raw42293 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42293step0 raw42293; decide +kernel
      have hl : raw42293step0Labels = raw42293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42293 raw42293Labels permutation434 hz
    mixedMoment B raw42293step0 raw42293step0Labels = mixedMoment B raw42293step1 raw42293step1Labels := by
      have ha : raw42293step1 = (fun i j => raw42293step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42293step1 raw42293step0; decide +kernel
      have hl : raw42293step1Labels = raw42293step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42293step0 raw42293step0Labels permutation151 permutation3
    mixedMoment B raw42293step1 raw42293step1Labels = mixedMoment B raw42293step2 raw42293step2Labels := by
      have ha : raw42293step2 = -raw42293step1 := by apply Matrix.ext; change ∀ i j, raw42293step2 i j = -(raw42293step1 i j); unfold raw42293step2 raw42293step1; decide +kernel
      have hl : raw42293step2Labels = raw42293step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42293step2 raw42293step2Labels = mixedMoment B raw42293step3 raw42293step3Labels := by
      have ha : raw42293step3 = raw42293step2 := by apply Matrix.ext; unfold raw42293step3 raw42293step2; decide +kernel
      have hl : raw42293step2Labels = labelEmbedding7 ∘ raw42293step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42293step2 raw42293step2Labels raw42293step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw42294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42294Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42294step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw42294step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42294step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42294step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42294step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42294 raw42294Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw42294 raw42294Labels = mixedMoment B raw42294step0 raw42294step0Labels := by
      have hz : ∀ j, raw42294 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42294step0 = (fun i j => raw42294 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42294step0 raw42294; decide +kernel
      have hl : raw42294step0Labels = raw42294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42294 raw42294Labels permutation434 hz
    mixedMoment B raw42294step0 raw42294step0Labels = mixedMoment B raw42294step1 raw42294step1Labels := by
      have ha : raw42294step1 = (fun i j => raw42294step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42294step1 raw42294step0; decide +kernel
      have hl : raw42294step1Labels = raw42294step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42294step0 raw42294step0Labels permutation151 permutation2
    mixedMoment B raw42294step1 raw42294step1Labels = mixedMoment B raw42294step2 raw42294step2Labels := by
      have ha : raw42294step2 = -raw42294step1 := by apply Matrix.ext; change ∀ i j, raw42294step2 i j = -(raw42294step1 i j); unfold raw42294step2 raw42294step1; decide +kernel
      have hl : raw42294step2Labels = raw42294step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42294step2 raw42294step2Labels = mixedMoment B raw42294step3 raw42294step3Labels := by
      have ha : raw42294step3 = raw42294step2 := by apply Matrix.ext; unfold raw42294step3 raw42294step2; decide +kernel
      have hl : raw42294step2Labels = labelEmbedding1 ∘ raw42294step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42294step2 raw42294step2Labels raw42294step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3565 node3565Labels := by rfl

def raw42295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42295Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42295step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42295step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42295step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42295step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42295 raw42295Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw42295 raw42295Labels = mixedMoment B raw42295step0 raw42295step0Labels := by
      have hz : ∀ j, raw42295 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42295step0 = (fun i j => raw42295 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42295step0 raw42295; decide +kernel
      have hl : raw42295step0Labels = raw42295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42295 raw42295Labels permutation434 hz
    mixedMoment B raw42295step0 raw42295step0Labels = mixedMoment B raw42295step1 raw42295step1Labels := by
      have ha : raw42295step1 = (fun i j => raw42295step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42295step1 raw42295step0; decide +kernel
      have hl : raw42295step1Labels = raw42295step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42295step0 raw42295step0Labels permutation144 permutation7
    mixedMoment B raw42295step1 raw42295step1Labels = mixedMoment B raw42295step2 raw42295step2Labels := by
      have ha : raw42295step2 = raw42295step1 := by apply Matrix.ext; unfold raw42295step2 raw42295step1; decide +kernel
      have hl : raw42295step1Labels = labelEmbedding6 ∘ raw42295step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42295step1 raw42295step1Labels raw42295step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5164 node5164Labels := by rfl

def raw42296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42296Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42296step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42296 raw42296Labels = mixedMoment B node3955 node3955Labels := by
  calc
    mixedMoment B raw42296 raw42296Labels = mixedMoment B raw42296step0 raw42296step0Labels := by
      have ha : raw42296step0 = (fun i j => raw42296 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42296step0 raw42296; decide +kernel
      have hl : raw42296step0Labels = raw42296Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42296 raw42296Labels permutation157 permutation2
    mixedMoment B raw42296step0 raw42296step0Labels = mixedMoment B raw42296step1 raw42296step1Labels := by
      have ha : raw42296step1 = raw42296step0 := by apply Matrix.ext; unfold raw42296step1 raw42296step0; decide +kernel
      have hl : raw42296step0Labels = labelEmbedding1 ∘ raw42296step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42296step0 raw42296step0Labels raw42296step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3955 node3955Labels := by rfl

def raw42297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42297Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw42297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42297step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw42297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42297 raw42297Labels = mixedMoment B node5470 node5470Labels := by
  calc
    mixedMoment B raw42297 raw42297Labels = mixedMoment B raw42297step0 raw42297step0Labels := by
      have ha : raw42297step0 = (fun i j => raw42297 (permutation337 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42297step0 raw42297; decide +kernel
      have hl : raw42297step0Labels = raw42297Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42297 raw42297Labels permutation337 permutation6
    mixedMoment B raw42297step0 raw42297step0Labels = mixedMoment B raw42297step1 raw42297step1Labels := by
      have ha : raw42297step1 = -raw42297step0 := by apply Matrix.ext; change ∀ i j, raw42297step1 i j = -(raw42297step0 i j); unfold raw42297step1 raw42297step0; decide +kernel
      have hl : raw42297step1Labels = raw42297step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5470 node5470Labels := by rfl

def raw42298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42298Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42298step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![2, -2, 0]]
def raw42298step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42298step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42298step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42298step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42298step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42298step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42298step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42298 raw42298Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw42298 raw42298Labels = mixedMoment B raw42298step0 raw42298step0Labels := by
      have hz : ∀ j, raw42298 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42298step0 = (fun i j => raw42298 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42298step0 raw42298; decide +kernel
      have hl : raw42298step0Labels = raw42298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42298 raw42298Labels permutation434 hz
    mixedMoment B raw42298step0 raw42298step0Labels = mixedMoment B raw42298step1 raw42298step1Labels := by
      have hz : ∀ j, raw42298step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42298step1 = (fun i j => raw42298step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42298step1 raw42298step0; decide +kernel
      have hl : raw42298step1Labels = raw42298step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42298step0 raw42298step0Labels permutation80 hz
    mixedMoment B raw42298step1 raw42298step1Labels = mixedMoment B raw42298step2 raw42298step2Labels := by
      have ha : raw42298step2 = (fun i j => raw42298step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42298step2 raw42298step1; decide +kernel
      have hl : raw42298step2Labels = raw42298step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42298step1 raw42298step1Labels permutation20 permutation4
    mixedMoment B raw42298step2 raw42298step2Labels = mixedMoment B raw42298step3 raw42298step3Labels := by
      have ha : raw42298step3 = -raw42298step2 := by apply Matrix.ext; change ∀ i j, raw42298step3 i j = -(raw42298step2 i j); unfold raw42298step3 raw42298step2; decide +kernel
      have hl : raw42298step3Labels = raw42298step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42298step3 raw42298step3Labels = mixedMoment B raw42298step4 raw42298step4Labels := by
      have ha : raw42298step4 = raw42298step3 := by apply Matrix.ext; unfold raw42298step4 raw42298step3; decide +kernel
      have hl : raw42298step3Labels = labelEmbedding1 ∘ raw42298step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42298step3 raw42298step3Labels raw42298step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3584 node3584Labels := by rfl

def raw42299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42299Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42299step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![2, -2, 0]]
def raw42299step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42299step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42299step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42299 raw42299Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw42299 raw42299Labels = mixedMoment B raw42299step0 raw42299step0Labels := by
      have hz : ∀ j, raw42299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42299step0 = (fun i j => raw42299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42299step0 raw42299; decide +kernel
      have hl : raw42299step0Labels = raw42299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42299 raw42299Labels permutation434 hz
    mixedMoment B raw42299step0 raw42299step0Labels = mixedMoment B raw42299step1 raw42299step1Labels := by
      have hz : ∀ j, raw42299step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42299step1 = (fun i j => raw42299step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42299step1 raw42299step0; decide +kernel
      have hl : raw42299step1Labels = raw42299step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42299step0 raw42299step0Labels permutation80 hz
    mixedMoment B raw42299step1 raw42299step1Labels = mixedMoment B raw42299step2 raw42299step2Labels := by
      have ha : raw42299step2 = (fun i j => raw42299step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42299step2 raw42299step1; decide +kernel
      have hl : raw42299step2Labels = raw42299step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42299step1 raw42299step1Labels permutation24 permutation6
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw42300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw42300Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw42300step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42300step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 2, -4]]
def raw42300step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42300step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw42300step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42300step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42300step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42300step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42300step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42300 raw42300Labels = mixedMoment B node3306 node3306Labels := by
  calc
    mixedMoment B raw42300 raw42300Labels = mixedMoment B raw42300step0 raw42300step0Labels := by
      have hz : ∀ j, raw42300 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42300step0 = (fun i j => raw42300 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42300step0 raw42300; decide +kernel
      have hl : raw42300step0Labels = raw42300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42300 raw42300Labels permutation434 hz
    mixedMoment B raw42300step0 raw42300step0Labels = mixedMoment B raw42300step1 raw42300step1Labels := by
      have hz : ∀ j, raw42300step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42300step1 = (fun i j => raw42300step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42300step1 raw42300step0; decide +kernel
      have hl : raw42300step1Labels = raw42300step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42300step0 raw42300step0Labels permutation80 hz
    mixedMoment B raw42300step1 raw42300step1Labels = mixedMoment B raw42300step2 raw42300step2Labels := by
      have ha : raw42300step2 = (fun i j => raw42300step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42300step2 raw42300step1; decide +kernel
      have hl : raw42300step2Labels = raw42300step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42300step1 raw42300step1Labels permutation31 permutation2
    mixedMoment B raw42300step2 raw42300step2Labels = mixedMoment B raw42300step3 raw42300step3Labels := by
      have ha : raw42300step3 = -raw42300step2 := by apply Matrix.ext; change ∀ i j, raw42300step3 i j = -(raw42300step2 i j); unfold raw42300step3 raw42300step2; decide +kernel
      have hl : raw42300step3Labels = raw42300step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42300step3 raw42300step3Labels = mixedMoment B raw42300step4 raw42300step4Labels := by
      have ha : raw42300step4 = raw42300step3 := by apply Matrix.ext; unfold raw42300step4 raw42300step3; decide +kernel
      have hl : raw42300step3Labels = labelEmbedding1 ∘ raw42300step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42300step3 raw42300step3Labels raw42300step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3306 node3306Labels := by rfl

def raw42301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw42301Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 2, -4]]
def raw42301step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![2, 2, -4]]
def raw42301step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42301step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42301step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42301 raw42301Labels = mixedMoment B node4620 node4620Labels := by
  calc
    mixedMoment B raw42301 raw42301Labels = mixedMoment B raw42301step0 raw42301step0Labels := by
      have hz : ∀ j, raw42301 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42301step0 = (fun i j => raw42301 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42301step0 raw42301; decide +kernel
      have hl : raw42301step0Labels = raw42301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42301 raw42301Labels permutation434 hz
    mixedMoment B raw42301step0 raw42301step0Labels = mixedMoment B raw42301step1 raw42301step1Labels := by
      have hz : ∀ j, raw42301step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42301step1 = (fun i j => raw42301step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42301step1 raw42301step0; decide +kernel
      have hl : raw42301step1Labels = raw42301step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42301step0 raw42301step0Labels permutation80 hz
    mixedMoment B raw42301step1 raw42301step1Labels = mixedMoment B raw42301step2 raw42301step2Labels := by
      have ha : raw42301step2 = (fun i j => raw42301step1 (permutation27 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42301step2 raw42301step1; decide +kernel
      have hl : raw42301step2Labels = raw42301step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42301step1 raw42301step1Labels permutation27 permutation6
    _ = mixedMoment B node4620 node4620Labels := by rfl

def raw42302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42302Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42302step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw42302step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42302step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42302step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42302step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw42302step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42302 raw42302Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw42302 raw42302Labels = mixedMoment B raw42302step0 raw42302step0Labels := by
      have hz : ∀ j, raw42302 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42302step0 = (fun i j => raw42302 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42302step0 raw42302; decide +kernel
      have hl : raw42302step0Labels = raw42302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42302 raw42302Labels permutation346 hz
    mixedMoment B raw42302step0 raw42302step0Labels = mixedMoment B raw42302step1 raw42302step1Labels := by
      have ha : raw42302step1 = (fun i j => raw42302step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42302step1 raw42302step0; decide +kernel
      have hl : raw42302step1Labels = raw42302step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42302step0 raw42302step0Labels permutation151 permutation2
    mixedMoment B raw42302step1 raw42302step1Labels = mixedMoment B raw42302step2 raw42302step2Labels := by
      have ha : raw42302step2 = -raw42302step1 := by apply Matrix.ext; change ∀ i j, raw42302step2 i j = -(raw42302step1 i j); unfold raw42302step2 raw42302step1; decide +kernel
      have hl : raw42302step2Labels = raw42302step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42302step2 raw42302step2Labels = mixedMoment B raw42302step3 raw42302step3Labels := by
      have ha : raw42302step3 = raw42302step2 := by apply Matrix.ext; unfold raw42302step3 raw42302step2; decide +kernel
      have hl : raw42302step2Labels = labelEmbedding1 ∘ raw42302step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42302step2 raw42302step2Labels raw42302step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

def raw42303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42303Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw42303step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw42303step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42303step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw42303step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42303 raw42303Labels = mixedMoment B node4603 node4603Labels := by
  calc
    mixedMoment B raw42303 raw42303Labels = mixedMoment B raw42303step0 raw42303step0Labels := by
      have hz : ∀ j, raw42303 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42303step0 = (fun i j => raw42303 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42303step0 raw42303; decide +kernel
      have hl : raw42303step0Labels = raw42303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42303 raw42303Labels permutation346 hz
    mixedMoment B raw42303step0 raw42303step0Labels = mixedMoment B raw42303step1 raw42303step1Labels := by
      have ha : raw42303step1 = (fun i j => raw42303step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42303step1 raw42303step0; decide +kernel
      have hl : raw42303step1Labels = raw42303step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42303step0 raw42303step0Labels permutation150 permutation7
    mixedMoment B raw42303step1 raw42303step1Labels = mixedMoment B raw42303step2 raw42303step2Labels := by
      have ha : raw42303step2 = raw42303step1 := by apply Matrix.ext; unfold raw42303step2 raw42303step1; decide +kernel
      have hl : raw42303step1Labels = labelEmbedding6 ∘ raw42303step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42303step1 raw42303step1Labels raw42303step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4603 node4603Labels := by rfl

def raw42304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42304Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42304step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw42304step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42304step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42304step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42304step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42304step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42304 raw42304Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw42304 raw42304Labels = mixedMoment B raw42304step0 raw42304step0Labels := by
      have hz : ∀ j, raw42304 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42304step0 = (fun i j => raw42304 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42304step0 raw42304; decide +kernel
      have hl : raw42304step0Labels = raw42304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42304 raw42304Labels permutation346 hz
    mixedMoment B raw42304step0 raw42304step0Labels = mixedMoment B raw42304step1 raw42304step1Labels := by
      have ha : raw42304step1 = (fun i j => raw42304step0 (permutation82 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42304step1 raw42304step0; decide +kernel
      have hl : raw42304step1Labels = raw42304step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42304step0 raw42304step0Labels permutation82 permutation4
    mixedMoment B raw42304step1 raw42304step1Labels = mixedMoment B raw42304step2 raw42304step2Labels := by
      have ha : raw42304step2 = -raw42304step1 := by apply Matrix.ext; change ∀ i j, raw42304step2 i j = -(raw42304step1 i j); unfold raw42304step2 raw42304step1; decide +kernel
      have hl : raw42304step2Labels = raw42304step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42304step2 raw42304step2Labels = mixedMoment B raw42304step3 raw42304step3Labels := by
      have ha : raw42304step3 = raw42304step2 := by apply Matrix.ext; unfold raw42304step3 raw42304step2; decide +kernel
      have hl : raw42304step2Labels = labelEmbedding1 ∘ raw42304step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42304step2 raw42304step2Labels raw42304step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3565 node3565Labels := by rfl

def raw42305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42305Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![1, 0, -1], ![1, -2, 1]]
def raw42305step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42305step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42305 raw42305Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw42305 raw42305Labels = mixedMoment B raw42305step0 raw42305step0Labels := by
      have hz : ∀ j, raw42305 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42305step0 = (fun i j => raw42305 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42305step0 raw42305; decide +kernel
      have hl : raw42305step0Labels = raw42305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42305 raw42305Labels permutation346 hz
    mixedMoment B raw42305step0 raw42305step0Labels = mixedMoment B raw42305step1 raw42305step1Labels := by
      have ha : raw42305step1 = (fun i j => raw42305step0 (permutation93 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42305step1 raw42305step0; decide +kernel
      have hl : raw42305step1Labels = raw42305step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42305step0 raw42305step0Labels permutation93 permutation6
    _ = mixedMoment B node5164 node5164Labels := by rfl

def raw42306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42306Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42306step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw42306step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42306step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42306step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42306step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42306step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42306 raw42306Labels = mixedMoment B node3580 node3580Labels := by
  calc
    mixedMoment B raw42306 raw42306Labels = mixedMoment B raw42306step0 raw42306step0Labels := by
      have hz : ∀ j, raw42306 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42306step0 = (fun i j => raw42306 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42306step0 raw42306; decide +kernel
      have hl : raw42306step0Labels = raw42306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42306 raw42306Labels permutation346 hz
    mixedMoment B raw42306step0 raw42306step0Labels = mixedMoment B raw42306step1 raw42306step1Labels := by
      have ha : raw42306step1 = (fun i j => raw42306step0 (permutation83 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42306step1 raw42306step0; decide +kernel
      have hl : raw42306step1Labels = raw42306step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42306step0 raw42306step0Labels permutation83 permutation4
    mixedMoment B raw42306step1 raw42306step1Labels = mixedMoment B raw42306step2 raw42306step2Labels := by
      have ha : raw42306step2 = -raw42306step1 := by apply Matrix.ext; change ∀ i j, raw42306step2 i j = -(raw42306step1 i j); unfold raw42306step2 raw42306step1; decide +kernel
      have hl : raw42306step2Labels = raw42306step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42306step2 raw42306step2Labels = mixedMoment B raw42306step3 raw42306step3Labels := by
      have ha : raw42306step3 = raw42306step2 := by apply Matrix.ext; unfold raw42306step3 raw42306step2; decide +kernel
      have hl : raw42306step2Labels = labelEmbedding1 ∘ raw42306step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42306step2 raw42306step2Labels raw42306step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3580 node3580Labels := by rfl

def raw42307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42307Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 2, -3], ![1, -1, 0], ![1, -1, 0]]
def raw42307step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42307step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42307 raw42307Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw42307 raw42307Labels = mixedMoment B raw42307step0 raw42307step0Labels := by
      have hz : ∀ j, raw42307 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42307step0 = (fun i j => raw42307 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42307step0 raw42307; decide +kernel
      have hl : raw42307step0Labels = raw42307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42307 raw42307Labels permutation346 hz
    mixedMoment B raw42307step0 raw42307step0Labels = mixedMoment B raw42307step1 raw42307step1Labels := by
      have ha : raw42307step1 = (fun i j => raw42307step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42307step1 raw42307step0; decide +kernel
      have hl : raw42307step1Labels = raw42307step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42307step0 raw42307step0Labels permutation96 permutation6
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw42308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42308Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42308step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42308step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42308step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42308step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42308 raw42308Labels = mixedMoment B node3960 node3960Labels := by
  calc
    mixedMoment B raw42308 raw42308Labels = mixedMoment B raw42308step0 raw42308step0Labels := by
      have hz : ∀ j, raw42308 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42308step0 = (fun i j => raw42308 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42308step0 raw42308; decide +kernel
      have hl : raw42308step0Labels = raw42308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42308 raw42308Labels permutation346 hz
    mixedMoment B raw42308step0 raw42308step0Labels = mixedMoment B raw42308step1 raw42308step1Labels := by
      have ha : raw42308step1 = (fun i j => raw42308step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42308step1 raw42308step0; decide +kernel
      have hl : raw42308step1Labels = raw42308step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42308step0 raw42308step0Labels permutation36 permutation2
    mixedMoment B raw42308step1 raw42308step1Labels = mixedMoment B raw42308step2 raw42308step2Labels := by
      have ha : raw42308step2 = raw42308step1 := by apply Matrix.ext; unfold raw42308step2 raw42308step1; decide +kernel
      have hl : raw42308step1Labels = labelEmbedding1 ∘ raw42308step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42308step1 raw42308step1Labels raw42308step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3960 node3960Labels := by rfl

def raw42309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42309Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![1, -2, 1]]
def raw42309step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42309step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42309 raw42309Labels = mixedMoment B node5463 node5463Labels := by
  calc
    mixedMoment B raw42309 raw42309Labels = mixedMoment B raw42309step0 raw42309step0Labels := by
      have hz : ∀ j, raw42309 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42309step0 = (fun i j => raw42309 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42309step0 raw42309; decide +kernel
      have hl : raw42309step0Labels = raw42309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42309 raw42309Labels permutation346 hz
    mixedMoment B raw42309step0 raw42309step0Labels = mixedMoment B raw42309step1 raw42309step1Labels := by
      have ha : raw42309step1 = (fun i j => raw42309step0 (permutation93 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42309step1 raw42309step0; decide +kernel
      have hl : raw42309step1Labels = raw42309step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42309step0 raw42309step0Labels permutation93 permutation6
    _ = mixedMoment B node5463 node5463Labels := by rfl

def raw42310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42310Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw42310step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42310step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42310step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42310step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42310step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42310 raw42310Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw42310 raw42310Labels = mixedMoment B raw42310step0 raw42310step0Labels := by
      have ha : raw42310step0 = (fun i j => raw42310 (permutation447 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42310step0 raw42310; decide +kernel
      have hl : raw42310step0Labels = raw42310Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42310 raw42310Labels permutation447 permutation4
    mixedMoment B raw42310step0 raw42310step0Labels = mixedMoment B raw42310step1 raw42310step1Labels := by
      have ha : raw42310step1 = -raw42310step0 := by apply Matrix.ext; change ∀ i j, raw42310step1 i j = -(raw42310step0 i j); unfold raw42310step1 raw42310step0; decide +kernel
      have hl : raw42310step1Labels = raw42310step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42310step1 raw42310step1Labels = mixedMoment B raw42310step2 raw42310step2Labels := by
      have ha : raw42310step2 = raw42310step1 := by apply Matrix.ext; unfold raw42310step2 raw42310step1; decide +kernel
      have hl : raw42310step1Labels = labelEmbedding1 ∘ raw42310step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42310step1 raw42310step1Labels raw42310step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

def raw42311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42311Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42311step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42311 raw42311Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw42311 raw42311Labels = mixedMoment B raw42311step0 raw42311step0Labels := by
      have ha : raw42311step0 = (fun i j => raw42311 (permutation500 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42311step0 raw42311; decide +kernel
      have hl : raw42311step0Labels = raw42311Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42311 raw42311Labels permutation500 permutation6
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw42312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42312Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42312step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42312step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42312step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42312 raw42312Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw42312 raw42312Labels = mixedMoment B raw42312step0 raw42312step0Labels := by
      have hz : ∀ j, raw42312 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42312step0 = (fun i j => raw42312 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42312step0 raw42312; decide +kernel
      have hl : raw42312step0Labels = raw42312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42312 raw42312Labels permutation434 hz
    mixedMoment B raw42312step0 raw42312step0Labels = mixedMoment B raw42312step1 raw42312step1Labels := by
      have ha : raw42312step1 = (fun i j => raw42312step0 (permutation72 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42312step1 raw42312step0; decide +kernel
      have hl : raw42312step1Labels = raw42312step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42312step0 raw42312step0Labels permutation72 permutation4
    mixedMoment B raw42312step1 raw42312step1Labels = mixedMoment B raw42312step2 raw42312step2Labels := by
      have ha : raw42312step2 = raw42312step1 := by apply Matrix.ext; unfold raw42312step2 raw42312step1; decide +kernel
      have hl : raw42312step1Labels = labelEmbedding1 ∘ raw42312step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42312step1 raw42312step1Labels raw42312step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3538 node3538Labels := by rfl

def raw42313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42313Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42313step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw42313step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw42313step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42313 raw42313Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw42313 raw42313Labels = mixedMoment B raw42313step0 raw42313step0Labels := by
      have hz : ∀ j, raw42313 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42313step0 = (fun i j => raw42313 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42313step0 raw42313; decide +kernel
      have hl : raw42313step0Labels = raw42313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42313 raw42313Labels permutation434 hz
    mixedMoment B raw42313step0 raw42313step0Labels = mixedMoment B raw42313step1 raw42313step1Labels := by
      have ha : raw42313step1 = (fun i j => raw42313step0 (permutation59 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42313step1 raw42313step0; decide +kernel
      have hl : raw42313step1Labels = raw42313step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42313step0 raw42313step0Labels permutation59 permutation6
    mixedMoment B raw42313step1 raw42313step1Labels = mixedMoment B raw42313step2 raw42313step2Labels := by
      have ha : raw42313step2 = -raw42313step1 := by apply Matrix.ext; change ∀ i j, raw42313step2 i j = -(raw42313step1 i j); unfold raw42313step2 raw42313step1; decide +kernel
      have hl : raw42313step2Labels = raw42313step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5188 node5188Labels := by rfl

def raw42314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42314Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42314step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42314step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42314step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42314 raw42314Labels = mixedMoment B node3524 node3524Labels := by
  calc
    mixedMoment B raw42314 raw42314Labels = mixedMoment B raw42314step0 raw42314step0Labels := by
      have ha : raw42314step0 = (fun i j => raw42314 (permutation342 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42314step0 raw42314; decide +kernel
      have hl : raw42314step0Labels = raw42314Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42314 raw42314Labels permutation342 permutation4
    mixedMoment B raw42314step0 raw42314step0Labels = mixedMoment B raw42314step1 raw42314step1Labels := by
      have ha : raw42314step1 = raw42314step0 := by apply Matrix.ext; unfold raw42314step1 raw42314step0; decide +kernel
      have hl : raw42314step0Labels = labelEmbedding1 ∘ raw42314step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42314step0 raw42314step0Labels raw42314step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3524 node3524Labels := by rfl

def raw42315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42315Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw42315step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42315step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42315step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42315 raw42315Labels = mixedMoment B node5184 node5184Labels := by
  calc
    mixedMoment B raw42315 raw42315Labels = mixedMoment B raw42315step0 raw42315step0Labels := by
      have ha : raw42315step0 = (fun i j => raw42315 (permutation286 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42315step0 raw42315; decide +kernel
      have hl : raw42315step0Labels = raw42315Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42315 raw42315Labels permutation286 permutation6
    mixedMoment B raw42315step0 raw42315step0Labels = mixedMoment B raw42315step1 raw42315step1Labels := by
      have ha : raw42315step1 = -raw42315step0 := by apply Matrix.ext; change ∀ i j, raw42315step1 i j = -(raw42315step0 i j); unfold raw42315step1 raw42315step0; decide +kernel
      have hl : raw42315step1Labels = raw42315step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5184 node5184Labels := by rfl

def raw42316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42316Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42316step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42316 raw42316Labels = mixedMoment B node3537 node3537Labels := by
  calc
    mixedMoment B raw42316 raw42316Labels = mixedMoment B raw42316step0 raw42316step0Labels := by
      have ha : raw42316step0 = (fun i j => raw42316 (permutation329 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42316step0 raw42316; decide +kernel
      have hl : raw42316step0Labels = raw42316Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42316 raw42316Labels permutation329 permutation4
    mixedMoment B raw42316step0 raw42316step0Labels = mixedMoment B raw42316step1 raw42316step1Labels := by
      have ha : raw42316step1 = raw42316step0 := by apply Matrix.ext; unfold raw42316step1 raw42316step0; decide +kernel
      have hl : raw42316step0Labels = labelEmbedding1 ∘ raw42316step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42316step0 raw42316step0Labels raw42316step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3537 node3537Labels := by rfl

def raw42317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42317Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42317step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42317step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42317step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42317 raw42317Labels = mixedMoment B node5187 node5187Labels := by
  calc
    mixedMoment B raw42317 raw42317Labels = mixedMoment B raw42317step0 raw42317step0Labels := by
      have ha : raw42317step0 = (fun i j => raw42317 (permutation277 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42317step0 raw42317; decide +kernel
      have hl : raw42317step0Labels = raw42317Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42317 raw42317Labels permutation277 permutation6
    mixedMoment B raw42317step0 raw42317step0Labels = mixedMoment B raw42317step1 raw42317step1Labels := by
      have ha : raw42317step1 = -raw42317step0 := by apply Matrix.ext; change ∀ i j, raw42317step1 i j = -(raw42317step0 i j); unfold raw42317step1 raw42317step0; decide +kernel
      have hl : raw42317step1Labels = raw42317step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5187 node5187Labels := by rfl

def raw42318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42318Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42318step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw42318step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw42318step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42318step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw42318step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42318 raw42318Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw42318 raw42318Labels = mixedMoment B raw42318step0 raw42318step0Labels := by
      have hz : ∀ j, raw42318 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42318step0 = (fun i j => raw42318 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42318step0 raw42318; decide +kernel
      have hl : raw42318step0Labels = raw42318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42318 raw42318Labels permutation434 hz
    mixedMoment B raw42318step0 raw42318step0Labels = mixedMoment B raw42318step1 raw42318step1Labels := by
      have ha : raw42318step1 = (fun i j => raw42318step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42318step1 raw42318step0; decide +kernel
      have hl : raw42318step1Labels = raw42318step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42318step0 raw42318step0Labels permutation151 permutation2
    mixedMoment B raw42318step1 raw42318step1Labels = mixedMoment B raw42318step2 raw42318step2Labels := by
      have ha : raw42318step2 = -raw42318step1 := by apply Matrix.ext; change ∀ i j, raw42318step2 i j = -(raw42318step1 i j); unfold raw42318step2 raw42318step1; decide +kernel
      have hl : raw42318step2Labels = raw42318step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42318step2 raw42318step2Labels = mixedMoment B raw42318step3 raw42318step3Labels := by
      have ha : raw42318step3 = raw42318step2 := by apply Matrix.ext; unfold raw42318step3 raw42318step2; decide +kernel
      have hl : raw42318step2Labels = labelEmbedding1 ∘ raw42318step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42318step2 raw42318step2Labels raw42318step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

def raw42319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42319Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw42319step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw42319step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42319step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw42319step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42319 raw42319Labels = mixedMoment B node5139 node5139Labels := by
  calc
    mixedMoment B raw42319 raw42319Labels = mixedMoment B raw42319step0 raw42319step0Labels := by
      have hz : ∀ j, raw42319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42319step0 = (fun i j => raw42319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42319step0 raw42319; decide +kernel
      have hl : raw42319step0Labels = raw42319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42319 raw42319Labels permutation434 hz
    mixedMoment B raw42319step0 raw42319step0Labels = mixedMoment B raw42319step1 raw42319step1Labels := by
      have ha : raw42319step1 = (fun i j => raw42319step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42319step1 raw42319step0; decide +kernel
      have hl : raw42319step1Labels = raw42319step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42319step0 raw42319step0Labels permutation144 permutation7
    mixedMoment B raw42319step1 raw42319step1Labels = mixedMoment B raw42319step2 raw42319step2Labels := by
      have ha : raw42319step2 = raw42319step1 := by apply Matrix.ext; unfold raw42319step2 raw42319step1; decide +kernel
      have hl : raw42319step1Labels = labelEmbedding6 ∘ raw42319step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42319step1 raw42319step1Labels raw42319step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5139 node5139Labels := by rfl

def raw42320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42320Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42320step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42320 raw42320Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw42320 raw42320Labels = mixedMoment B raw42320step0 raw42320step0Labels := by
      have ha : raw42320step0 = (fun i j => raw42320 (permutation344 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42320step0 raw42320; decide +kernel
      have hl : raw42320step0Labels = raw42320Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42320 raw42320Labels permutation344 permutation4
    mixedMoment B raw42320step0 raw42320step0Labels = mixedMoment B raw42320step1 raw42320step1Labels := by
      have ha : raw42320step1 = raw42320step0 := by apply Matrix.ext; unfold raw42320step1 raw42320step0; decide +kernel
      have hl : raw42320step0Labels = labelEmbedding1 ∘ raw42320step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42320step0 raw42320step0Labels raw42320step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

def raw42321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42321Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw42321step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42321step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw42321step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42321 raw42321Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw42321 raw42321Labels = mixedMoment B raw42321step0 raw42321step0Labels := by
      have ha : raw42321step0 = (fun i j => raw42321 (permutation287 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42321step0 raw42321; decide +kernel
      have hl : raw42321step0Labels = raw42321Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42321 raw42321Labels permutation287 permutation6
    mixedMoment B raw42321step0 raw42321step0Labels = mixedMoment B raw42321step1 raw42321step1Labels := by
      have ha : raw42321step1 = -raw42321step0 := by apply Matrix.ext; change ∀ i j, raw42321step1 i j = -(raw42321step0 i j); unfold raw42321step1 raw42321step0; decide +kernel
      have hl : raw42321step1Labels = raw42321step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5185 node5185Labels := by rfl

def raw42322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42322Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42322step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 2, -4]]
def raw42322step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42322step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw42322step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42322step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw42322step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42322step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw42322step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42322 raw42322Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw42322 raw42322Labels = mixedMoment B raw42322step0 raw42322step0Labels := by
      have hz : ∀ j, raw42322 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42322step0 = (fun i j => raw42322 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42322step0 raw42322; decide +kernel
      have hl : raw42322step0Labels = raw42322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42322 raw42322Labels permutation434 hz
    mixedMoment B raw42322step0 raw42322step0Labels = mixedMoment B raw42322step1 raw42322step1Labels := by
      have hz : ∀ j, raw42322step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42322step1 = (fun i j => raw42322step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42322step1 raw42322step0; decide +kernel
      have hl : raw42322step1Labels = raw42322step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42322step0 raw42322step0Labels permutation80 hz
    mixedMoment B raw42322step1 raw42322step1Labels = mixedMoment B raw42322step2 raw42322step2Labels := by
      have ha : raw42322step2 = (fun i j => raw42322step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42322step2 raw42322step1; decide +kernel
      have hl : raw42322step2Labels = raw42322step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42322step1 raw42322step1Labels permutation31 permutation2
    mixedMoment B raw42322step2 raw42322step2Labels = mixedMoment B raw42322step3 raw42322step3Labels := by
      have ha : raw42322step3 = -raw42322step2 := by apply Matrix.ext; change ∀ i j, raw42322step3 i j = -(raw42322step2 i j); unfold raw42322step3 raw42322step2; decide +kernel
      have hl : raw42322step3Labels = raw42322step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42322step3 raw42322step3Labels = mixedMoment B raw42322step4 raw42322step4Labels := by
      have ha : raw42322step4 = raw42322step3 := by apply Matrix.ext; unfold raw42322step4 raw42322step3; decide +kernel
      have hl : raw42322step3Labels = labelEmbedding1 ∘ raw42322step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42322step3 raw42322step3Labels raw42322step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3302 node3302Labels := by rfl

def raw42323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42323Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 2, -4]]
def raw42323step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42323step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, -1, 0], ![2, 2, -4]]
def raw42323step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42323step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw42323step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42323step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw42323step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42323 raw42323Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw42323 raw42323Labels = mixedMoment B raw42323step0 raw42323step0Labels := by
      have hz : ∀ j, raw42323 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42323step0 = (fun i j => raw42323 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42323step0 raw42323; decide +kernel
      have hl : raw42323step0Labels = raw42323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42323 raw42323Labels permutation434 hz
    mixedMoment B raw42323step0 raw42323step0Labels = mixedMoment B raw42323step1 raw42323step1Labels := by
      have hz : ∀ j, raw42323step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42323step1 = (fun i j => raw42323step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42323step1 raw42323step0; decide +kernel
      have hl : raw42323step1Labels = raw42323step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42323step0 raw42323step0Labels permutation80 hz
    mixedMoment B raw42323step1 raw42323step1Labels = mixedMoment B raw42323step2 raw42323step2Labels := by
      have ha : raw42323step2 = (fun i j => raw42323step1 (permutation30 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42323step2 raw42323step1; decide +kernel
      have hl : raw42323step2Labels = raw42323step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42323step1 raw42323step1Labels permutation30 permutation7
    mixedMoment B raw42323step2 raw42323step2Labels = mixedMoment B raw42323step3 raw42323step3Labels := by
      have ha : raw42323step3 = raw42323step2 := by apply Matrix.ext; unfold raw42323step3 raw42323step2; decide +kernel
      have hl : raw42323step2Labels = labelEmbedding6 ∘ raw42323step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42323step2 raw42323step2Labels raw42323step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4609 node4609Labels := by rfl

def raw42324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42324Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42324step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42324step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw42324step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42324 raw42324Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw42324 raw42324Labels = mixedMoment B raw42324step0 raw42324step0Labels := by
      have hz : ∀ j, raw42324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42324step0 = (fun i j => raw42324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42324step0 raw42324; decide +kernel
      have hl : raw42324step0Labels = raw42324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42324 raw42324Labels permutation346 hz
    mixedMoment B raw42324step0 raw42324step0Labels = mixedMoment B raw42324step1 raw42324step1Labels := by
      have ha : raw42324step1 = (fun i j => raw42324step0 (permutation78 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42324step1 raw42324step0; decide +kernel
      have hl : raw42324step1Labels = raw42324step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42324step0 raw42324step0Labels permutation78 permutation4
    mixedMoment B raw42324step1 raw42324step1Labels = mixedMoment B raw42324step2 raw42324step2Labels := by
      have ha : raw42324step2 = raw42324step1 := by apply Matrix.ext; unfold raw42324step2 raw42324step1; decide +kernel
      have hl : raw42324step1Labels = labelEmbedding1 ∘ raw42324step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42324step1 raw42324step1Labels raw42324step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

def raw42325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42325Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, 2, -3], ![1, 0, -1], ![1, -1, 0]]
def raw42325step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw42325step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42325 raw42325Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw42325 raw42325Labels = mixedMoment B raw42325step0 raw42325step0Labels := by
      have hz : ∀ j, raw42325 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42325step0 = (fun i j => raw42325 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42325step0 raw42325; decide +kernel
      have hl : raw42325step0Labels = raw42325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42325 raw42325Labels permutation346 hz
    mixedMoment B raw42325step0 raw42325step0Labels = mixedMoment B raw42325step1 raw42325step1Labels := by
      have ha : raw42325step1 = (fun i j => raw42325step0 (permutation96 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42325step1 raw42325step0; decide +kernel
      have hl : raw42325step1Labels = raw42325step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42325step0 raw42325step0Labels permutation96 permutation6
    _ = mixedMoment B node5147 node5147Labels := by rfl

def raw42326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42326Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42326step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42326step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw42326step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42326 raw42326Labels = mixedMoment B node3542 node3542Labels := by
  calc
    mixedMoment B raw42326 raw42326Labels = mixedMoment B raw42326step0 raw42326step0Labels := by
      have hz : ∀ j, raw42326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42326step0 = (fun i j => raw42326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42326step0 raw42326; decide +kernel
      have hl : raw42326step0Labels = raw42326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42326 raw42326Labels permutation346 hz
    mixedMoment B raw42326step0 raw42326step0Labels = mixedMoment B raw42326step1 raw42326step1Labels := by
      have ha : raw42326step1 = (fun i j => raw42326step0 (permutation74 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42326step1 raw42326step0; decide +kernel
      have hl : raw42326step1Labels = raw42326step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42326step0 raw42326step0Labels permutation74 permutation4
    mixedMoment B raw42326step1 raw42326step1Labels = mixedMoment B raw42326step2 raw42326step2Labels := by
      have ha : raw42326step2 = raw42326step1 := by apply Matrix.ext; unfold raw42326step2 raw42326step1; decide +kernel
      have hl : raw42326step1Labels = labelEmbedding1 ∘ raw42326step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42326step1 raw42326step1Labels raw42326step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3542 node3542Labels := by rfl

def raw42327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42327Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -2, 3], ![1, 1, -2], ![1, 1, -2], ![1, -1, 0]]
def raw42327step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw42327step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw42327step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42327 raw42327Labels = mixedMoment B node5189 node5189Labels := by
  calc
    mixedMoment B raw42327 raw42327Labels = mixedMoment B raw42327step0 raw42327step0Labels := by
      have hz : ∀ j, raw42327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42327step0 = (fun i j => raw42327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42327step0 raw42327; decide +kernel
      have hl : raw42327step0Labels = raw42327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42327 raw42327Labels permutation346 hz
    mixedMoment B raw42327step0 raw42327step0Labels = mixedMoment B raw42327step1 raw42327step1Labels := by
      have ha : raw42327step1 = (fun i j => raw42327step0 (permutation60 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42327step1 raw42327step0; decide +kernel
      have hl : raw42327step1Labels = raw42327step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42327step0 raw42327step0Labels permutation60 permutation6
    mixedMoment B raw42327step1 raw42327step1Labels = mixedMoment B raw42327step2 raw42327step2Labels := by
      have ha : raw42327step2 = -raw42327step1 := by apply Matrix.ext; change ∀ i j, raw42327step2 i j = -(raw42327step1 i j); unfold raw42327step2 raw42327step1; decide +kernel
      have hl : raw42327step2Labels = raw42327step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5189 node5189Labels := by rfl

def raw42328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42328Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42328step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42328step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![3, -3, 0]]
def raw42328step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42328step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![3, -3, 0]]
def raw42328step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42328step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-3, 3, 0]]
def raw42328step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42328step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw42328step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42328step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![3, -3, 0]]
def raw42328step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42328 raw42328Labels = mixedMoment B node2778 node2778Labels := by
  calc
    mixedMoment B raw42328 raw42328Labels = mixedMoment B raw42328step0 raw42328step0Labels := by
      have hz : ∀ j, raw42328 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42328step0 = (fun i j => raw42328 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42328step0 raw42328; decide +kernel
      have hl : raw42328step0Labels = raw42328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42328 raw42328Labels permutation520 hz
    mixedMoment B raw42328step0 raw42328step0Labels = mixedMoment B raw42328step1 raw42328step1Labels := by
      have hz : ∀ j, raw42328step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42328step1 = (fun i j => raw42328step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42328step1 raw42328step0; decide +kernel
      have hl : raw42328step1Labels = raw42328step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42328step0 raw42328step0Labels permutation104 hz
    mixedMoment B raw42328step1 raw42328step1Labels = mixedMoment B raw42328step2 raw42328step2Labels := by
      have hz : ∀ j, raw42328step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw42328step2 = (fun i j => raw42328step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw42328step2 raw42328step1; decide +kernel
      have hl : raw42328step2Labels = raw42328step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42328step1 raw42328step1Labels permutation20 hz
    mixedMoment B raw42328step2 raw42328step2Labels = mixedMoment B raw42328step3 raw42328step3Labels := by
      have ha : raw42328step3 = (fun i j => raw42328step2 (permutation4 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42328step3 raw42328step2; decide +kernel
      have hl : raw42328step3Labels = raw42328step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42328step2 raw42328step2Labels permutation4 permutation4
    mixedMoment B raw42328step3 raw42328step3Labels = mixedMoment B raw42328step4 raw42328step4Labels := by
      have ha : raw42328step4 = -raw42328step3 := by apply Matrix.ext; change ∀ i j, raw42328step4 i j = -(raw42328step3 i j); unfold raw42328step4 raw42328step3; decide +kernel
      have hl : raw42328step4Labels = raw42328step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42328step4 raw42328step4Labels = mixedMoment B raw42328step5 raw42328step5Labels := by
      have ha : raw42328step5 = raw42328step4 := by apply Matrix.ext; unfold raw42328step5 raw42328step4; decide +kernel
      have hl : raw42328step4Labels = labelEmbedding1 ∘ raw42328step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42328step4 raw42328step4Labels raw42328step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2778 node2778Labels := by rfl

def raw42329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42329Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42329step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![3, -3, 0]]
def raw42329step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42329step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![3, -3, 0]]
def raw42329step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42329step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw42329step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42329step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw42329step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42329 raw42329Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw42329 raw42329Labels = mixedMoment B raw42329step0 raw42329step0Labels := by
      have hz : ∀ j, raw42329 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42329step0 = (fun i j => raw42329 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42329step0 raw42329; decide +kernel
      have hl : raw42329step0Labels = raw42329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42329 raw42329Labels permutation520 hz
    mixedMoment B raw42329step0 raw42329step0Labels = mixedMoment B raw42329step1 raw42329step1Labels := by
      have hz : ∀ j, raw42329step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42329step1 = (fun i j => raw42329step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42329step1 raw42329step0; decide +kernel
      have hl : raw42329step1Labels = raw42329step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42329step0 raw42329step0Labels permutation104 hz
    mixedMoment B raw42329step1 raw42329step1Labels = mixedMoment B raw42329step2 raw42329step2Labels := by
      have hz : ∀ j, raw42329step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw42329step2 = (fun i j => raw42329step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw42329step2 raw42329step1; decide +kernel
      have hl : raw42329step2Labels = raw42329step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42329step1 raw42329step1Labels permutation20 hz
    mixedMoment B raw42329step2 raw42329step2Labels = mixedMoment B raw42329step3 raw42329step3Labels := by
      have ha : raw42329step3 = (fun i j => raw42329step2 (permutation6 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42329step3 raw42329step2; decide +kernel
      have hl : raw42329step3Labels = raw42329step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42329step2 raw42329step2Labels permutation6 permutation5
    mixedMoment B raw42329step3 raw42329step3Labels = mixedMoment B raw42329step4 raw42329step4Labels := by
      have ha : raw42329step4 = raw42329step3 := by apply Matrix.ext; unfold raw42329step4 raw42329step3; decide +kernel
      have hl : raw42329step3Labels = labelEmbedding9 ∘ raw42329step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42329step3 raw42329step3Labels raw42329step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

def raw42330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42330Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42330step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, 0, -1], ![2, -3, 1]]
def raw42330step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42330step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw42330step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42330step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw42330step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42330step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw42330step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42330 raw42330Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw42330 raw42330Labels = mixedMoment B raw42330step0 raw42330step0Labels := by
      have hz : ∀ j, raw42330 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42330step0 = (fun i j => raw42330 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42330step0 raw42330; decide +kernel
      have hl : raw42330step0Labels = raw42330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42330 raw42330Labels permutation434 hz
    mixedMoment B raw42330step0 raw42330step0Labels = mixedMoment B raw42330step1 raw42330step1Labels := by
      have hz : ∀ j, raw42330step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42330step1 = (fun i j => raw42330step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42330step1 raw42330step0; decide +kernel
      have hl : raw42330step1Labels = raw42330step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42330step0 raw42330step0Labels permutation80 hz
    mixedMoment B raw42330step1 raw42330step1Labels = mixedMoment B raw42330step2 raw42330step2Labels := by
      have ha : raw42330step2 = (fun i j => raw42330step1 (permutation16 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42330step2 raw42330step1; decide +kernel
      have hl : raw42330step2Labels = raw42330step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42330step1 raw42330step1Labels permutation16 permutation4
    mixedMoment B raw42330step2 raw42330step2Labels = mixedMoment B raw42330step3 raw42330step3Labels := by
      have ha : raw42330step3 = -raw42330step2 := by apply Matrix.ext; change ∀ i j, raw42330step3 i j = -(raw42330step2 i j); unfold raw42330step3 raw42330step2; decide +kernel
      have hl : raw42330step3Labels = raw42330step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42330step3 raw42330step3Labels = mixedMoment B raw42330step4 raw42330step4Labels := by
      have ha : raw42330step4 = raw42330step3 := by apply Matrix.ext; unfold raw42330step4 raw42330step3; decide +kernel
      have hl : raw42330step3Labels = labelEmbedding1 ∘ raw42330step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42330step3 raw42330step3Labels raw42330step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw42331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42331Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42331step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42331step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, 0, -1], ![2, -3, 1]]
def raw42331step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42331step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw42331step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42331step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw42331step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42331step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw42331step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42331 raw42331Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw42331 raw42331Labels = mixedMoment B raw42331step0 raw42331step0Labels := by
      have hz : ∀ j, raw42331 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42331step0 = (fun i j => raw42331 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42331step0 raw42331; decide +kernel
      have hl : raw42331step0Labels = raw42331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42331 raw42331Labels permutation434 hz
    mixedMoment B raw42331step0 raw42331step0Labels = mixedMoment B raw42331step1 raw42331step1Labels := by
      have hz : ∀ j, raw42331step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42331step1 = (fun i j => raw42331step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42331step1 raw42331step0; decide +kernel
      have hl : raw42331step1Labels = raw42331step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42331step0 raw42331step0Labels permutation80 hz
    mixedMoment B raw42331step1 raw42331step1Labels = mixedMoment B raw42331step2 raw42331step2Labels := by
      have ha : raw42331step2 = (fun i j => raw42331step1 (permutation16 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42331step2 raw42331step1; decide +kernel
      have hl : raw42331step2Labels = raw42331step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42331step1 raw42331step1Labels permutation16 permutation4
    mixedMoment B raw42331step2 raw42331step2Labels = mixedMoment B raw42331step3 raw42331step3Labels := by
      have ha : raw42331step3 = -raw42331step2 := by apply Matrix.ext; change ∀ i j, raw42331step3 i j = -(raw42331step2 i j); unfold raw42331step3 raw42331step2; decide +kernel
      have hl : raw42331step3Labels = raw42331step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42331step3 raw42331step3Labels = mixedMoment B raw42331step4 raw42331step4Labels := by
      have ha : raw42331step4 = raw42331step3 := by apply Matrix.ext; unfold raw42331step4 raw42331step3; decide +kernel
      have hl : raw42331step3Labels = labelEmbedding10 ∘ raw42331step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42331step3 raw42331step3Labels raw42331step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5268 node5268Labels := by rfl

def raw42332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42332Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42332step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42332step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42332step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw42332step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42332step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42332step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42332step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42332step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42332 raw42332Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw42332 raw42332Labels = mixedMoment B raw42332step0 raw42332step0Labels := by
      have hz : ∀ j, raw42332 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42332step0 = (fun i j => raw42332 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42332step0 raw42332; decide +kernel
      have hl : raw42332step0Labels = raw42332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42332 raw42332Labels permutation434 hz
    mixedMoment B raw42332step0 raw42332step0Labels = mixedMoment B raw42332step1 raw42332step1Labels := by
      have hz : ∀ j, raw42332step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42332step1 = (fun i j => raw42332step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42332step1 raw42332step0; decide +kernel
      have hl : raw42332step1Labels = raw42332step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42332step0 raw42332step0Labels permutation80 hz
    mixedMoment B raw42332step1 raw42332step1Labels = mixedMoment B raw42332step2 raw42332step2Labels := by
      have ha : raw42332step2 = (fun i j => raw42332step1 (permutation14 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42332step2 raw42332step1; decide +kernel
      have hl : raw42332step2Labels = raw42332step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42332step1 raw42332step1Labels permutation14 permutation4
    mixedMoment B raw42332step2 raw42332step2Labels = mixedMoment B raw42332step3 raw42332step3Labels := by
      have ha : raw42332step3 = -raw42332step2 := by apply Matrix.ext; change ∀ i j, raw42332step3 i j = -(raw42332step2 i j); unfold raw42332step3 raw42332step2; decide +kernel
      have hl : raw42332step3Labels = raw42332step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42332step3 raw42332step3Labels = mixedMoment B raw42332step4 raw42332step4Labels := by
      have ha : raw42332step4 = raw42332step3 := by apply Matrix.ext; unfold raw42332step4 raw42332step3; decide +kernel
      have hl : raw42332step3Labels = labelEmbedding1 ∘ raw42332step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42332step3 raw42332step3Labels raw42332step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2776 node2776Labels := by rfl

def raw42333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42333Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42333step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42333step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42333step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw42333step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42333step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42333step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42333step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42333step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42333 raw42333Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw42333 raw42333Labels = mixedMoment B raw42333step0 raw42333step0Labels := by
      have hz : ∀ j, raw42333 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42333step0 = (fun i j => raw42333 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42333step0 raw42333; decide +kernel
      have hl : raw42333step0Labels = raw42333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42333 raw42333Labels permutation434 hz
    mixedMoment B raw42333step0 raw42333step0Labels = mixedMoment B raw42333step1 raw42333step1Labels := by
      have hz : ∀ j, raw42333step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42333step1 = (fun i j => raw42333step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42333step1 raw42333step0; decide +kernel
      have hl : raw42333step1Labels = raw42333step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42333step0 raw42333step0Labels permutation80 hz
    mixedMoment B raw42333step1 raw42333step1Labels = mixedMoment B raw42333step2 raw42333step2Labels := by
      have ha : raw42333step2 = (fun i j => raw42333step1 (permutation14 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42333step2 raw42333step1; decide +kernel
      have hl : raw42333step2Labels = raw42333step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42333step1 raw42333step1Labels permutation14 permutation4
    mixedMoment B raw42333step2 raw42333step2Labels = mixedMoment B raw42333step3 raw42333step3Labels := by
      have ha : raw42333step3 = -raw42333step2 := by apply Matrix.ext; change ∀ i j, raw42333step3 i j = -(raw42333step2 i j); unfold raw42333step3 raw42333step2; decide +kernel
      have hl : raw42333step3Labels = raw42333step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42333step3 raw42333step3Labels = mixedMoment B raw42333step4 raw42333step4Labels := by
      have ha : raw42333step4 = raw42333step3 := by apply Matrix.ext; unfold raw42333step4 raw42333step3; decide +kernel
      have hl : raw42333step3Labels = labelEmbedding10 ∘ raw42333step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42333step3 raw42333step3Labels raw42333step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw42334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42334Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42334step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42334step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42334step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw42334step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42334step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42334step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42334step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42334step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42334 raw42334Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw42334 raw42334Labels = mixedMoment B raw42334step0 raw42334step0Labels := by
      have hz : ∀ j, raw42334 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42334step0 = (fun i j => raw42334 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42334step0 raw42334; decide +kernel
      have hl : raw42334step0Labels = raw42334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42334 raw42334Labels permutation434 hz
    mixedMoment B raw42334step0 raw42334step0Labels = mixedMoment B raw42334step1 raw42334step1Labels := by
      have hz : ∀ j, raw42334step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42334step1 = (fun i j => raw42334step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42334step1 raw42334step0; decide +kernel
      have hl : raw42334step1Labels = raw42334step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42334step0 raw42334step0Labels permutation80 hz
    mixedMoment B raw42334step1 raw42334step1Labels = mixedMoment B raw42334step2 raw42334step2Labels := by
      have ha : raw42334step2 = (fun i j => raw42334step1 (permutation15 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42334step2 raw42334step1; decide +kernel
      have hl : raw42334step2Labels = raw42334step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42334step1 raw42334step1Labels permutation15 permutation4
    mixedMoment B raw42334step2 raw42334step2Labels = mixedMoment B raw42334step3 raw42334step3Labels := by
      have ha : raw42334step3 = -raw42334step2 := by apply Matrix.ext; change ∀ i j, raw42334step3 i j = -(raw42334step2 i j); unfold raw42334step3 raw42334step2; decide +kernel
      have hl : raw42334step3Labels = raw42334step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42334step3 raw42334step3Labels = mixedMoment B raw42334step4 raw42334step4Labels := by
      have ha : raw42334step4 = raw42334step3 := by apply Matrix.ext; unfold raw42334step4 raw42334step3; decide +kernel
      have hl : raw42334step3Labels = labelEmbedding1 ∘ raw42334step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42334step3 raw42334step3Labels raw42334step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2774 node2774Labels := by rfl

def raw42335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42335Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42335step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42335step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42335step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42335step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw42335step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42335step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42335step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42335step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42335step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42335 raw42335Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw42335 raw42335Labels = mixedMoment B raw42335step0 raw42335step0Labels := by
      have hz : ∀ j, raw42335 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42335step0 = (fun i j => raw42335 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42335step0 raw42335; decide +kernel
      have hl : raw42335step0Labels = raw42335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42335 raw42335Labels permutation434 hz
    mixedMoment B raw42335step0 raw42335step0Labels = mixedMoment B raw42335step1 raw42335step1Labels := by
      have hz : ∀ j, raw42335step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42335step1 = (fun i j => raw42335step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42335step1 raw42335step0; decide +kernel
      have hl : raw42335step1Labels = raw42335step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42335step0 raw42335step0Labels permutation80 hz
    mixedMoment B raw42335step1 raw42335step1Labels = mixedMoment B raw42335step2 raw42335step2Labels := by
      have ha : raw42335step2 = (fun i j => raw42335step1 (permutation15 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42335step2 raw42335step1; decide +kernel
      have hl : raw42335step2Labels = raw42335step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42335step1 raw42335step1Labels permutation15 permutation4
    mixedMoment B raw42335step2 raw42335step2Labels = mixedMoment B raw42335step3 raw42335step3Labels := by
      have ha : raw42335step3 = -raw42335step2 := by apply Matrix.ext; change ∀ i j, raw42335step3 i j = -(raw42335step2 i j); unfold raw42335step3 raw42335step2; decide +kernel
      have hl : raw42335step3Labels = raw42335step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42335step3 raw42335step3Labels = mixedMoment B raw42335step4 raw42335step4Labels := by
      have ha : raw42335step4 = raw42335step3 := by apply Matrix.ext; unfold raw42335step4 raw42335step3; decide +kernel
      have hl : raw42335step3Labels = labelEmbedding10 ∘ raw42335step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42335step3 raw42335step3Labels raw42335step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw42336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42336Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42336step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -3, 2], ![2, 0, -2]]
def raw42336step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42336step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw42336step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42336step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw42336step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42336 raw42336Labels = mixedMoment B node2680 node2680Labels := by
  calc
    mixedMoment B raw42336 raw42336Labels = mixedMoment B raw42336step0 raw42336step0Labels := by
      have hz : ∀ j, raw42336 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42336step0 = (fun i j => raw42336 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42336step0 raw42336; decide +kernel
      have hl : raw42336step0Labels = raw42336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42336 raw42336Labels permutation434 hz
    mixedMoment B raw42336step0 raw42336step0Labels = mixedMoment B raw42336step1 raw42336step1Labels := by
      have hz : ∀ j, raw42336step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42336step1 = (fun i j => raw42336step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42336step1 raw42336step0; decide +kernel
      have hl : raw42336step1Labels = raw42336step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42336step0 raw42336step0Labels permutation80 hz
    mixedMoment B raw42336step1 raw42336step1Labels = mixedMoment B raw42336step2 raw42336step2Labels := by
      have ha : raw42336step2 = (fun i j => raw42336step1 (permutation21 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42336step2 raw42336step1; decide +kernel
      have hl : raw42336step2Labels = raw42336step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42336step1 raw42336step1Labels permutation21 permutation4
    mixedMoment B raw42336step2 raw42336step2Labels = mixedMoment B raw42336step3 raw42336step3Labels := by
      have ha : raw42336step3 = raw42336step2 := by apply Matrix.ext; unfold raw42336step3 raw42336step2; decide +kernel
      have hl : raw42336step2Labels = labelEmbedding1 ∘ raw42336step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42336step2 raw42336step2Labels raw42336step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2680 node2680Labels := by rfl

def raw42337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42337Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42337step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -3, 2], ![2, 0, -2]]
def raw42337step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42337step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw42337step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42337step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw42337step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42337 raw42337Labels = mixedMoment B node5235 node5235Labels := by
  calc
    mixedMoment B raw42337 raw42337Labels = mixedMoment B raw42337step0 raw42337step0Labels := by
      have hz : ∀ j, raw42337 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42337step0 = (fun i j => raw42337 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42337step0 raw42337; decide +kernel
      have hl : raw42337step0Labels = raw42337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42337 raw42337Labels permutation434 hz
    mixedMoment B raw42337step0 raw42337step0Labels = mixedMoment B raw42337step1 raw42337step1Labels := by
      have hz : ∀ j, raw42337step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42337step1 = (fun i j => raw42337step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42337step1 raw42337step0; decide +kernel
      have hl : raw42337step1Labels = raw42337step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42337step0 raw42337step0Labels permutation80 hz
    mixedMoment B raw42337step1 raw42337step1Labels = mixedMoment B raw42337step2 raw42337step2Labels := by
      have ha : raw42337step2 = (fun i j => raw42337step1 (permutation21 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42337step2 raw42337step1; decide +kernel
      have hl : raw42337step2Labels = raw42337step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42337step1 raw42337step1Labels permutation21 permutation4
    mixedMoment B raw42337step2 raw42337step2Labels = mixedMoment B raw42337step3 raw42337step3Labels := by
      have ha : raw42337step3 = raw42337step2 := by apply Matrix.ext; unfold raw42337step3 raw42337step2; decide +kernel
      have hl : raw42337step2Labels = labelEmbedding10 ∘ raw42337step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42337step2 raw42337step2Labels raw42337step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5235 node5235Labels := by rfl

def raw42338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42338Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42338step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42338step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42338step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42338step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42338step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42338step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42338 raw42338Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw42338 raw42338Labels = mixedMoment B raw42338step0 raw42338step0Labels := by
      have hz : ∀ j, raw42338 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42338step0 = (fun i j => raw42338 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42338step0 raw42338; decide +kernel
      have hl : raw42338step0Labels = raw42338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42338 raw42338Labels permutation346 hz
    mixedMoment B raw42338step0 raw42338step0Labels = mixedMoment B raw42338step1 raw42338step1Labels := by
      have ha : raw42338step1 = (fun i j => raw42338step0 (permutation68 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42338step1 raw42338step0; decide +kernel
      have hl : raw42338step1Labels = raw42338step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42338step0 raw42338step0Labels permutation68 permutation4
    mixedMoment B raw42338step1 raw42338step1Labels = mixedMoment B raw42338step2 raw42338step2Labels := by
      have ha : raw42338step2 = -raw42338step1 := by apply Matrix.ext; change ∀ i j, raw42338step2 i j = -(raw42338step1 i j); unfold raw42338step2 raw42338step1; decide +kernel
      have hl : raw42338step2Labels = raw42338step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42338step2 raw42338step2Labels = mixedMoment B raw42338step3 raw42338step3Labels := by
      have ha : raw42338step3 = raw42338step2 := by apply Matrix.ext; unfold raw42338step3 raw42338step2; decide +kernel
      have hl : raw42338step2Labels = labelEmbedding1 ∘ raw42338step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42338step2 raw42338step2Labels raw42338step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw42339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42339Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42339step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42339step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42339step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42339step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42339step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42339step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42339 raw42339Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw42339 raw42339Labels = mixedMoment B raw42339step0 raw42339step0Labels := by
      have hz : ∀ j, raw42339 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42339step0 = (fun i j => raw42339 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42339step0 raw42339; decide +kernel
      have hl : raw42339step0Labels = raw42339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42339 raw42339Labels permutation346 hz
    mixedMoment B raw42339step0 raw42339step0Labels = mixedMoment B raw42339step1 raw42339step1Labels := by
      have ha : raw42339step1 = (fun i j => raw42339step0 (permutation68 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42339step1 raw42339step0; decide +kernel
      have hl : raw42339step1Labels = raw42339step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42339step0 raw42339step0Labels permutation68 permutation4
    mixedMoment B raw42339step1 raw42339step1Labels = mixedMoment B raw42339step2 raw42339step2Labels := by
      have ha : raw42339step2 = -raw42339step1 := by apply Matrix.ext; change ∀ i j, raw42339step2 i j = -(raw42339step1 i j); unfold raw42339step2 raw42339step1; decide +kernel
      have hl : raw42339step2Labels = raw42339step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42339step2 raw42339step2Labels = mixedMoment B raw42339step3 raw42339step3Labels := by
      have ha : raw42339step3 = raw42339step2 := by apply Matrix.ext; unfold raw42339step3 raw42339step2; decide +kernel
      have hl : raw42339step2Labels = labelEmbedding10 ∘ raw42339step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42339step2 raw42339step2Labels raw42339step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw42340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42340Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42340step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw42340step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42340step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42340step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42340step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42340step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42340 raw42340Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw42340 raw42340Labels = mixedMoment B raw42340step0 raw42340step0Labels := by
      have hz : ∀ j, raw42340 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42340step0 = (fun i j => raw42340 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42340step0 raw42340; decide +kernel
      have hl : raw42340step0Labels = raw42340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42340 raw42340Labels permutation346 hz
    mixedMoment B raw42340step0 raw42340step0Labels = mixedMoment B raw42340step1 raw42340step1Labels := by
      have ha : raw42340step1 = (fun i j => raw42340step0 (permutation61 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42340step1 raw42340step0; decide +kernel
      have hl : raw42340step1Labels = raw42340step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42340step0 raw42340step0Labels permutation61 permutation4
    mixedMoment B raw42340step1 raw42340step1Labels = mixedMoment B raw42340step2 raw42340step2Labels := by
      have ha : raw42340step2 = -raw42340step1 := by apply Matrix.ext; change ∀ i j, raw42340step2 i j = -(raw42340step1 i j); unfold raw42340step2 raw42340step1; decide +kernel
      have hl : raw42340step2Labels = raw42340step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42340step2 raw42340step2Labels = mixedMoment B raw42340step3 raw42340step3Labels := by
      have ha : raw42340step3 = raw42340step2 := by apply Matrix.ext; unfold raw42340step3 raw42340step2; decide +kernel
      have hl : raw42340step2Labels = labelEmbedding1 ∘ raw42340step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42340step2 raw42340step2Labels raw42340step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw42341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42341Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42341step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw42341step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42341step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42341step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42341step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42341step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42341 raw42341Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw42341 raw42341Labels = mixedMoment B raw42341step0 raw42341step0Labels := by
      have hz : ∀ j, raw42341 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42341step0 = (fun i j => raw42341 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42341step0 raw42341; decide +kernel
      have hl : raw42341step0Labels = raw42341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42341 raw42341Labels permutation346 hz
    mixedMoment B raw42341step0 raw42341step0Labels = mixedMoment B raw42341step1 raw42341step1Labels := by
      have ha : raw42341step1 = (fun i j => raw42341step0 (permutation61 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42341step1 raw42341step0; decide +kernel
      have hl : raw42341step1Labels = raw42341step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42341step0 raw42341step0Labels permutation61 permutation4
    mixedMoment B raw42341step1 raw42341step1Labels = mixedMoment B raw42341step2 raw42341step2Labels := by
      have ha : raw42341step2 = -raw42341step1 := by apply Matrix.ext; change ∀ i j, raw42341step2 i j = -(raw42341step1 i j); unfold raw42341step2 raw42341step1; decide +kernel
      have hl : raw42341step2Labels = raw42341step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42341step2 raw42341step2Labels = mixedMoment B raw42341step3 raw42341step3Labels := by
      have ha : raw42341step3 = raw42341step2 := by apply Matrix.ext; unfold raw42341step3 raw42341step2; decide +kernel
      have hl : raw42341step2Labels = labelEmbedding10 ∘ raw42341step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42341step2 raw42341step2Labels raw42341step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw42342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42342Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42342step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42342step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42342step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42342step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42342step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42342step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42342 raw42342Labels = mixedMoment B node2678 node2678Labels := by
  calc
    mixedMoment B raw42342 raw42342Labels = mixedMoment B raw42342step0 raw42342step0Labels := by
      have hz : ∀ j, raw42342 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42342step0 = (fun i j => raw42342 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42342step0 raw42342; decide +kernel
      have hl : raw42342step0Labels = raw42342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42342 raw42342Labels permutation346 hz
    mixedMoment B raw42342step0 raw42342step0Labels = mixedMoment B raw42342step1 raw42342step1Labels := by
      have ha : raw42342step1 = (fun i j => raw42342step0 (permutation74 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42342step1 raw42342step0; decide +kernel
      have hl : raw42342step1Labels = raw42342step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42342step0 raw42342step0Labels permutation74 permutation4
    mixedMoment B raw42342step1 raw42342step1Labels = mixedMoment B raw42342step2 raw42342step2Labels := by
      have ha : raw42342step2 = -raw42342step1 := by apply Matrix.ext; change ∀ i j, raw42342step2 i j = -(raw42342step1 i j); unfold raw42342step2 raw42342step1; decide +kernel
      have hl : raw42342step2Labels = raw42342step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42342step2 raw42342step2Labels = mixedMoment B raw42342step3 raw42342step3Labels := by
      have ha : raw42342step3 = raw42342step2 := by apply Matrix.ext; unfold raw42342step3 raw42342step2; decide +kernel
      have hl : raw42342step2Labels = labelEmbedding1 ∘ raw42342step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42342step2 raw42342step2Labels raw42342step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2678 node2678Labels := by rfl

def raw42343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42343Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42343step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42343step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42343step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42343step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42343step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42343step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42343 raw42343Labels = mixedMoment B node5233 node5233Labels := by
  calc
    mixedMoment B raw42343 raw42343Labels = mixedMoment B raw42343step0 raw42343step0Labels := by
      have hz : ∀ j, raw42343 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42343step0 = (fun i j => raw42343 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42343step0 raw42343; decide +kernel
      have hl : raw42343step0Labels = raw42343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42343 raw42343Labels permutation346 hz
    mixedMoment B raw42343step0 raw42343step0Labels = mixedMoment B raw42343step1 raw42343step1Labels := by
      have ha : raw42343step1 = (fun i j => raw42343step0 (permutation74 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42343step1 raw42343step0; decide +kernel
      have hl : raw42343step1Labels = raw42343step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42343step0 raw42343step0Labels permutation74 permutation4
    mixedMoment B raw42343step1 raw42343step1Labels = mixedMoment B raw42343step2 raw42343step2Labels := by
      have ha : raw42343step2 = -raw42343step1 := by apply Matrix.ext; change ∀ i j, raw42343step2 i j = -(raw42343step1 i j); unfold raw42343step2 raw42343step1; decide +kernel
      have hl : raw42343step2Labels = raw42343step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42343step2 raw42343step2Labels = mixedMoment B raw42343step3 raw42343step3Labels := by
      have ha : raw42343step3 = raw42343step2 := by apply Matrix.ext; unfold raw42343step3 raw42343step2; decide +kernel
      have hl : raw42343step2Labels = labelEmbedding10 ∘ raw42343step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42343step2 raw42343step2Labels raw42343step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5233 node5233Labels := by rfl

def raw42344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42344Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42344step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42344step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42344step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42344step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42344step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42344step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42344 raw42344Labels = mixedMoment B node2677 node2677Labels := by
  calc
    mixedMoment B raw42344 raw42344Labels = mixedMoment B raw42344step0 raw42344step0Labels := by
      have hz : ∀ j, raw42344 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42344step0 = (fun i j => raw42344 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42344step0 raw42344; decide +kernel
      have hl : raw42344step0Labels = raw42344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42344 raw42344Labels permutation346 hz
    mixedMoment B raw42344step0 raw42344step0Labels = mixedMoment B raw42344step1 raw42344step1Labels := by
      have ha : raw42344step1 = (fun i j => raw42344step0 (permutation75 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42344step1 raw42344step0; decide +kernel
      have hl : raw42344step1Labels = raw42344step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42344step0 raw42344step0Labels permutation75 permutation4
    mixedMoment B raw42344step1 raw42344step1Labels = mixedMoment B raw42344step2 raw42344step2Labels := by
      have ha : raw42344step2 = -raw42344step1 := by apply Matrix.ext; change ∀ i j, raw42344step2 i j = -(raw42344step1 i j); unfold raw42344step2 raw42344step1; decide +kernel
      have hl : raw42344step2Labels = raw42344step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42344step2 raw42344step2Labels = mixedMoment B raw42344step3 raw42344step3Labels := by
      have ha : raw42344step3 = raw42344step2 := by apply Matrix.ext; unfold raw42344step3 raw42344step2; decide +kernel
      have hl : raw42344step2Labels = labelEmbedding1 ∘ raw42344step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42344step2 raw42344step2Labels raw42344step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2677 node2677Labels := by rfl

def raw42345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42345Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42345step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42345step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42345step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42345step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42345step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42345step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42345 raw42345Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw42345 raw42345Labels = mixedMoment B raw42345step0 raw42345step0Labels := by
      have hz : ∀ j, raw42345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42345step0 = (fun i j => raw42345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42345step0 raw42345; decide +kernel
      have hl : raw42345step0Labels = raw42345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42345 raw42345Labels permutation346 hz
    mixedMoment B raw42345step0 raw42345step0Labels = mixedMoment B raw42345step1 raw42345step1Labels := by
      have ha : raw42345step1 = (fun i j => raw42345step0 (permutation75 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42345step1 raw42345step0; decide +kernel
      have hl : raw42345step1Labels = raw42345step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42345step0 raw42345step0Labels permutation75 permutation4
    mixedMoment B raw42345step1 raw42345step1Labels = mixedMoment B raw42345step2 raw42345step2Labels := by
      have ha : raw42345step2 = -raw42345step1 := by apply Matrix.ext; change ∀ i j, raw42345step2 i j = -(raw42345step1 i j); unfold raw42345step2 raw42345step1; decide +kernel
      have hl : raw42345step2Labels = raw42345step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42345step2 raw42345step2Labels = mixedMoment B raw42345step3 raw42345step3Labels := by
      have ha : raw42345step3 = raw42345step2 := by apply Matrix.ext; unfold raw42345step3 raw42345step2; decide +kernel
      have hl : raw42345step2Labels = labelEmbedding10 ∘ raw42345step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42345step2 raw42345step2Labels raw42345step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

def raw42346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42346Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42346step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw42346step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42346step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw42346step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42346 raw42346Labels = mixedMoment B node2664 node2664Labels := by
  calc
    mixedMoment B raw42346 raw42346Labels = mixedMoment B raw42346step0 raw42346step0Labels := by
      have hz : ∀ j, raw42346 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42346step0 = (fun i j => raw42346 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42346step0 raw42346; decide +kernel
      have hl : raw42346step0Labels = raw42346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42346 raw42346Labels permutation346 hz
    mixedMoment B raw42346step0 raw42346step0Labels = mixedMoment B raw42346step1 raw42346step1Labels := by
      have ha : raw42346step1 = (fun i j => raw42346step0 (permutation131 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42346step1 raw42346step0; decide +kernel
      have hl : raw42346step1Labels = raw42346step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42346step0 raw42346step0Labels permutation131 permutation4
    mixedMoment B raw42346step1 raw42346step1Labels = mixedMoment B raw42346step2 raw42346step2Labels := by
      have ha : raw42346step2 = raw42346step1 := by apply Matrix.ext; unfold raw42346step2 raw42346step1; decide +kernel
      have hl : raw42346step1Labels = labelEmbedding1 ∘ raw42346step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42346step1 raw42346step1Labels raw42346step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2664 node2664Labels := by rfl

def raw42347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42347Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42347step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw42347step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42347step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw42347step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42347 raw42347Labels = mixedMoment B node5222 node5222Labels := by
  calc
    mixedMoment B raw42347 raw42347Labels = mixedMoment B raw42347step0 raw42347step0Labels := by
      have hz : ∀ j, raw42347 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42347step0 = (fun i j => raw42347 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42347step0 raw42347; decide +kernel
      have hl : raw42347step0Labels = raw42347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42347 raw42347Labels permutation346 hz
    mixedMoment B raw42347step0 raw42347step0Labels = mixedMoment B raw42347step1 raw42347step1Labels := by
      have ha : raw42347step1 = (fun i j => raw42347step0 (permutation131 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42347step1 raw42347step0; decide +kernel
      have hl : raw42347step1Labels = raw42347step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42347step0 raw42347step0Labels permutation131 permutation4
    mixedMoment B raw42347step1 raw42347step1Labels = mixedMoment B raw42347step2 raw42347step2Labels := by
      have ha : raw42347step2 = raw42347step1 := by apply Matrix.ext; unfold raw42347step2 raw42347step1; decide +kernel
      have hl : raw42347step1Labels = labelEmbedding10 ∘ raw42347step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42347step1 raw42347step1Labels raw42347step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5222 node5222Labels := by rfl

def raw42348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42348Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42348step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw42348step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42348step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42348step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42348step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42348step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42348 raw42348Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw42348 raw42348Labels = mixedMoment B raw42348step0 raw42348step0Labels := by
      have hz : ∀ j, raw42348 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42348step0 = (fun i j => raw42348 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42348step0 raw42348; decide +kernel
      have hl : raw42348step0Labels = raw42348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42348 raw42348Labels permutation346 hz
    mixedMoment B raw42348step0 raw42348step0Labels = mixedMoment B raw42348step1 raw42348step1Labels := by
      have ha : raw42348step1 = (fun i j => raw42348step0 (permutation62 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42348step1 raw42348step0; decide +kernel
      have hl : raw42348step1Labels = raw42348step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42348step0 raw42348step0Labels permutation62 permutation4
    mixedMoment B raw42348step1 raw42348step1Labels = mixedMoment B raw42348step2 raw42348step2Labels := by
      have ha : raw42348step2 = -raw42348step1 := by apply Matrix.ext; change ∀ i j, raw42348step2 i j = -(raw42348step1 i j); unfold raw42348step2 raw42348step1; decide +kernel
      have hl : raw42348step2Labels = raw42348step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42348step2 raw42348step2Labels = mixedMoment B raw42348step3 raw42348step3Labels := by
      have ha : raw42348step3 = raw42348step2 := by apply Matrix.ext; unfold raw42348step3 raw42348step2; decide +kernel
      have hl : raw42348step2Labels = labelEmbedding1 ∘ raw42348step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42348step2 raw42348step2Labels raw42348step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw42349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42349Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42349step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw42349step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42349step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42349step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42349step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42349step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42349 raw42349Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw42349 raw42349Labels = mixedMoment B raw42349step0 raw42349step0Labels := by
      have hz : ∀ j, raw42349 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42349step0 = (fun i j => raw42349 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42349step0 raw42349; decide +kernel
      have hl : raw42349step0Labels = raw42349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42349 raw42349Labels permutation346 hz
    mixedMoment B raw42349step0 raw42349step0Labels = mixedMoment B raw42349step1 raw42349step1Labels := by
      have ha : raw42349step1 = (fun i j => raw42349step0 (permutation62 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42349step1 raw42349step0; decide +kernel
      have hl : raw42349step1Labels = raw42349step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42349step0 raw42349step0Labels permutation62 permutation4
    mixedMoment B raw42349step1 raw42349step1Labels = mixedMoment B raw42349step2 raw42349step2Labels := by
      have ha : raw42349step2 = -raw42349step1 := by apply Matrix.ext; change ∀ i j, raw42349step2 i j = -(raw42349step1 i j); unfold raw42349step2 raw42349step1; decide +kernel
      have hl : raw42349step2Labels = raw42349step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42349step2 raw42349step2Labels = mixedMoment B raw42349step3 raw42349step3Labels := by
      have ha : raw42349step3 = raw42349step2 := by apply Matrix.ext; unfold raw42349step3 raw42349step2; decide +kernel
      have hl : raw42349step2Labels = labelEmbedding10 ∘ raw42349step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42349step2 raw42349step2Labels raw42349step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw42350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42350Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42350step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw42350step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42350step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42350step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42350step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42350 raw42350Labels = mixedMoment B node2775 node2775Labels := by
  calc
    mixedMoment B raw42350 raw42350Labels = mixedMoment B raw42350step0 raw42350step0Labels := by
      have hz : ∀ j, raw42350 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42350step0 = (fun i j => raw42350 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42350step0 raw42350; decide +kernel
      have hl : raw42350step0Labels = raw42350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42350 raw42350Labels permutation346 hz
    mixedMoment B raw42350step0 raw42350step0Labels = mixedMoment B raw42350step1 raw42350step1Labels := by
      have ha : raw42350step1 = (fun i j => raw42350step0 (permutation56 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42350step1 raw42350step0; decide +kernel
      have hl : raw42350step1Labels = raw42350step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42350step0 raw42350step0Labels permutation56 permutation4
    mixedMoment B raw42350step1 raw42350step1Labels = mixedMoment B raw42350step2 raw42350step2Labels := by
      have ha : raw42350step2 = -raw42350step1 := by apply Matrix.ext; change ∀ i j, raw42350step2 i j = -(raw42350step1 i j); unfold raw42350step2 raw42350step1; decide +kernel
      have hl : raw42350step2Labels = raw42350step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42350step2 raw42350step2Labels = mixedMoment B raw42350step3 raw42350step3Labels := by
      have ha : raw42350step3 = raw42350step2 := by apply Matrix.ext; unfold raw42350step3 raw42350step2; decide +kernel
      have hl : raw42350step2Labels = labelEmbedding1 ∘ raw42350step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42350step2 raw42350step2Labels raw42350step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2775 node2775Labels := by rfl

def raw42351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42351Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42351step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw42351step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42351step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42351step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42351step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42351step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42351 raw42351Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw42351 raw42351Labels = mixedMoment B raw42351step0 raw42351step0Labels := by
      have hz : ∀ j, raw42351 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42351step0 = (fun i j => raw42351 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42351step0 raw42351; decide +kernel
      have hl : raw42351step0Labels = raw42351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42351 raw42351Labels permutation346 hz
    mixedMoment B raw42351step0 raw42351step0Labels = mixedMoment B raw42351step1 raw42351step1Labels := by
      have ha : raw42351step1 = (fun i j => raw42351step0 (permutation56 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42351step1 raw42351step0; decide +kernel
      have hl : raw42351step1Labels = raw42351step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42351step0 raw42351step0Labels permutation56 permutation4
    mixedMoment B raw42351step1 raw42351step1Labels = mixedMoment B raw42351step2 raw42351step2Labels := by
      have ha : raw42351step2 = -raw42351step1 := by apply Matrix.ext; change ∀ i j, raw42351step2 i j = -(raw42351step1 i j); unfold raw42351step2 raw42351step1; decide +kernel
      have hl : raw42351step2Labels = raw42351step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42351step2 raw42351step2Labels = mixedMoment B raw42351step3 raw42351step3Labels := by
      have ha : raw42351step3 = raw42351step2 := by apply Matrix.ext; unfold raw42351step3 raw42351step2; decide +kernel
      have hl : raw42351step2Labels = labelEmbedding10 ∘ raw42351step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42351step2 raw42351step2Labels raw42351step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw42352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42352Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw42352step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42352step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42352step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42352step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42352 raw42352Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw42352 raw42352Labels = mixedMoment B raw42352step0 raw42352step0Labels := by
      have ha : raw42352step0 = (fun i j => raw42352 (permutation337 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42352step0 raw42352; decide +kernel
      have hl : raw42352step0Labels = raw42352Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42352 raw42352Labels permutation337 permutation4
    mixedMoment B raw42352step0 raw42352step0Labels = mixedMoment B raw42352step1 raw42352step1Labels := by
      have ha : raw42352step1 = -raw42352step0 := by apply Matrix.ext; change ∀ i j, raw42352step1 i j = -(raw42352step0 i j); unfold raw42352step1 raw42352step0; decide +kernel
      have hl : raw42352step1Labels = raw42352step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42352step1 raw42352step1Labels = mixedMoment B raw42352step2 raw42352step2Labels := by
      have ha : raw42352step2 = raw42352step1 := by apply Matrix.ext; unfold raw42352step2 raw42352step1; decide +kernel
      have hl : raw42352step1Labels = labelEmbedding1 ∘ raw42352step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42352step1 raw42352step1Labels raw42352step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2676 node2676Labels := by rfl

def raw42353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42353Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw42353step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42353step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42353step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42353step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42353step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42353 raw42353Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw42353 raw42353Labels = mixedMoment B raw42353step0 raw42353step0Labels := by
      have ha : raw42353step0 = (fun i j => raw42353 (permutation337 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42353step0 raw42353; decide +kernel
      have hl : raw42353step0Labels = raw42353Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42353 raw42353Labels permutation337 permutation4
    mixedMoment B raw42353step0 raw42353step0Labels = mixedMoment B raw42353step1 raw42353step1Labels := by
      have ha : raw42353step1 = -raw42353step0 := by apply Matrix.ext; change ∀ i j, raw42353step1 i j = -(raw42353step0 i j); unfold raw42353step1 raw42353step0; decide +kernel
      have hl : raw42353step1Labels = raw42353step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42353step1 raw42353step1Labels = mixedMoment B raw42353step2 raw42353step2Labels := by
      have ha : raw42353step2 = raw42353step1 := by apply Matrix.ext; unfold raw42353step2 raw42353step1; decide +kernel
      have hl : raw42353step1Labels = labelEmbedding10 ∘ raw42353step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42353step1 raw42353step1Labels raw42353step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

def raw42354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42354Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42354step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42354step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42354step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42354step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42354step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42354 raw42354Labels = mixedMoment B node2698 node2698Labels := by
  calc
    mixedMoment B raw42354 raw42354Labels = mixedMoment B raw42354step0 raw42354step0Labels := by
      have ha : raw42354step0 = (fun i j => raw42354 (permutation313 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42354step0 raw42354; decide +kernel
      have hl : raw42354step0Labels = raw42354Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42354 raw42354Labels permutation313 permutation4
    mixedMoment B raw42354step0 raw42354step0Labels = mixedMoment B raw42354step1 raw42354step1Labels := by
      have ha : raw42354step1 = -raw42354step0 := by apply Matrix.ext; change ∀ i j, raw42354step1 i j = -(raw42354step0 i j); unfold raw42354step1 raw42354step0; decide +kernel
      have hl : raw42354step1Labels = raw42354step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42354step1 raw42354step1Labels = mixedMoment B raw42354step2 raw42354step2Labels := by
      have ha : raw42354step2 = raw42354step1 := by apply Matrix.ext; unfold raw42354step2 raw42354step1; decide +kernel
      have hl : raw42354step1Labels = labelEmbedding1 ∘ raw42354step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42354step1 raw42354step1Labels raw42354step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2698 node2698Labels := by rfl

def raw42355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42355Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42355step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42355step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42355step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42355step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42355step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42355step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42355 raw42355Labels = mixedMoment B node5244 node5244Labels := by
  calc
    mixedMoment B raw42355 raw42355Labels = mixedMoment B raw42355step0 raw42355step0Labels := by
      have ha : raw42355step0 = (fun i j => raw42355 (permutation313 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42355step0 raw42355; decide +kernel
      have hl : raw42355step0Labels = raw42355Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42355 raw42355Labels permutation313 permutation4
    mixedMoment B raw42355step0 raw42355step0Labels = mixedMoment B raw42355step1 raw42355step1Labels := by
      have ha : raw42355step1 = -raw42355step0 := by apply Matrix.ext; change ∀ i j, raw42355step1 i j = -(raw42355step0 i j); unfold raw42355step1 raw42355step0; decide +kernel
      have hl : raw42355step1Labels = raw42355step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42355step1 raw42355step1Labels = mixedMoment B raw42355step2 raw42355step2Labels := by
      have ha : raw42355step2 = raw42355step1 := by apply Matrix.ext; unfold raw42355step2 raw42355step1; decide +kernel
      have hl : raw42355step1Labels = labelEmbedding10 ∘ raw42355step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42355step1 raw42355step1Labels raw42355step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5244 node5244Labels := by rfl

def raw42356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42356Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42356step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42356step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42356step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42356step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42356step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42356 raw42356Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw42356 raw42356Labels = mixedMoment B raw42356step0 raw42356step0Labels := by
      have ha : raw42356step0 = (fun i j => raw42356 (permutation308 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42356step0 raw42356; decide +kernel
      have hl : raw42356step0Labels = raw42356Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42356 raw42356Labels permutation308 permutation4
    mixedMoment B raw42356step0 raw42356step0Labels = mixedMoment B raw42356step1 raw42356step1Labels := by
      have ha : raw42356step1 = -raw42356step0 := by apply Matrix.ext; change ∀ i j, raw42356step1 i j = -(raw42356step0 i j); unfold raw42356step1 raw42356step0; decide +kernel
      have hl : raw42356step1Labels = raw42356step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42356step1 raw42356step1Labels = mixedMoment B raw42356step2 raw42356step2Labels := by
      have ha : raw42356step2 = raw42356step1 := by apply Matrix.ext; unfold raw42356step2 raw42356step1; decide +kernel
      have hl : raw42356step1Labels = labelEmbedding1 ∘ raw42356step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42356step1 raw42356step1Labels raw42356step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2730 node2730Labels := by rfl

def raw42357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42357Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42357step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42357step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42357step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42357step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42357step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42357 raw42357Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw42357 raw42357Labels = mixedMoment B raw42357step0 raw42357step0Labels := by
      have ha : raw42357step0 = (fun i j => raw42357 (permutation308 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42357step0 raw42357; decide +kernel
      have hl : raw42357step0Labels = raw42357Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42357 raw42357Labels permutation308 permutation4
    mixedMoment B raw42357step0 raw42357step0Labels = mixedMoment B raw42357step1 raw42357step1Labels := by
      have ha : raw42357step1 = -raw42357step0 := by apply Matrix.ext; change ∀ i j, raw42357step1 i j = -(raw42357step0 i j); unfold raw42357step1 raw42357step0; decide +kernel
      have hl : raw42357step1Labels = raw42357step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42357step1 raw42357step1Labels = mixedMoment B raw42357step2 raw42357step2Labels := by
      have ha : raw42357step2 = raw42357step1 := by apply Matrix.ext; unfold raw42357step2 raw42357step1; decide +kernel
      have hl : raw42357step1Labels = labelEmbedding10 ∘ raw42357step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42357step1 raw42357step1Labels raw42357step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw42358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42358Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42358step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42358step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42358step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42358step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42358step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42358 raw42358Labels = mixedMoment B node2697 node2697Labels := by
  calc
    mixedMoment B raw42358 raw42358Labels = mixedMoment B raw42358step0 raw42358step0Labels := by
      have ha : raw42358step0 = (fun i j => raw42358 (permutation314 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42358step0 raw42358; decide +kernel
      have hl : raw42358step0Labels = raw42358Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42358 raw42358Labels permutation314 permutation4
    mixedMoment B raw42358step0 raw42358step0Labels = mixedMoment B raw42358step1 raw42358step1Labels := by
      have ha : raw42358step1 = -raw42358step0 := by apply Matrix.ext; change ∀ i j, raw42358step1 i j = -(raw42358step0 i j); unfold raw42358step1 raw42358step0; decide +kernel
      have hl : raw42358step1Labels = raw42358step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42358step1 raw42358step1Labels = mixedMoment B raw42358step2 raw42358step2Labels := by
      have ha : raw42358step2 = raw42358step1 := by apply Matrix.ext; unfold raw42358step2 raw42358step1; decide +kernel
      have hl : raw42358step1Labels = labelEmbedding1 ∘ raw42358step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42358step1 raw42358step1Labels raw42358step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2697 node2697Labels := by rfl

def raw42359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 3, -2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42359Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw42359step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42359step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42359step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42359step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw42359step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42359 raw42359Labels = mixedMoment B node5243 node5243Labels := by
  calc
    mixedMoment B raw42359 raw42359Labels = mixedMoment B raw42359step0 raw42359step0Labels := by
      have ha : raw42359step0 = (fun i j => raw42359 (permutation314 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42359step0 raw42359; decide +kernel
      have hl : raw42359step0Labels = raw42359Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42359 raw42359Labels permutation314 permutation4
    mixedMoment B raw42359step0 raw42359step0Labels = mixedMoment B raw42359step1 raw42359step1Labels := by
      have ha : raw42359step1 = -raw42359step0 := by apply Matrix.ext; change ∀ i j, raw42359step1 i j = -(raw42359step0 i j); unfold raw42359step1 raw42359step0; decide +kernel
      have hl : raw42359step1Labels = raw42359step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42359step1 raw42359step1Labels = mixedMoment B raw42359step2 raw42359step2Labels := by
      have ha : raw42359step2 = raw42359step1 := by apply Matrix.ext; unfold raw42359step2 raw42359step1; decide +kernel
      have hl : raw42359step1Labels = labelEmbedding10 ∘ raw42359step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42359step1 raw42359step1Labels raw42359step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5243 node5243Labels := by rfl

def raw42360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42360Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42360step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42360step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42360step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw42360step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42360step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw42360step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42360 raw42360Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw42360 raw42360Labels = mixedMoment B raw42360step0 raw42360step0Labels := by
      have hz : ∀ j, raw42360 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42360step0 = (fun i j => raw42360 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42360step0 raw42360; decide +kernel
      have hl : raw42360step0Labels = raw42360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42360 raw42360Labels permutation520 hz
    mixedMoment B raw42360step0 raw42360step0Labels = mixedMoment B raw42360step1 raw42360step1Labels := by
      have hz : ∀ j, raw42360step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42360step1 = (fun i j => raw42360step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42360step1 raw42360step0; decide +kernel
      have hl : raw42360step1Labels = raw42360step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42360step0 raw42360step0Labels permutation104 hz
    mixedMoment B raw42360step1 raw42360step1Labels = mixedMoment B raw42360step2 raw42360step2Labels := by
      have ha : raw42360step2 = (fun i j => raw42360step1 (permutation27 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42360step2 raw42360step1; decide +kernel
      have hl : raw42360step2Labels = raw42360step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42360step1 raw42360step1Labels permutation27 permutation4
    mixedMoment B raw42360step2 raw42360step2Labels = mixedMoment B raw42360step3 raw42360step3Labels := by
      have ha : raw42360step3 = raw42360step2 := by apply Matrix.ext; unfold raw42360step3 raw42360step2; decide +kernel
      have hl : raw42360step2Labels = labelEmbedding1 ∘ raw42360step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42360step2 raw42360step2Labels raw42360step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3225 node3225Labels := by rfl

def raw42361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42361Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42361step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42361step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42361step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42361step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42361step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42361step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42361step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42361step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42361step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42361 raw42361Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw42361 raw42361Labels = mixedMoment B raw42361step0 raw42361step0Labels := by
      have hz : ∀ j, raw42361 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42361step0 = (fun i j => raw42361 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42361step0 raw42361; decide +kernel
      have hl : raw42361step0Labels = raw42361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42361 raw42361Labels permutation520 hz
    mixedMoment B raw42361step0 raw42361step0Labels = mixedMoment B raw42361step1 raw42361step1Labels := by
      have hz : ∀ j, raw42361step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42361step1 = (fun i j => raw42361step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42361step1 raw42361step0; decide +kernel
      have hl : raw42361step1Labels = raw42361step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42361step0 raw42361step0Labels permutation104 hz
    mixedMoment B raw42361step1 raw42361step1Labels = mixedMoment B raw42361step2 raw42361step2Labels := by
      have ha : raw42361step2 = (fun i j => raw42361step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42361step2 raw42361step1; decide +kernel
      have hl : raw42361step2Labels = raw42361step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42361step1 raw42361step1Labels permutation31 permutation3
    mixedMoment B raw42361step2 raw42361step2Labels = mixedMoment B raw42361step3 raw42361step3Labels := by
      have ha : raw42361step3 = -raw42361step2 := by apply Matrix.ext; change ∀ i j, raw42361step3 i j = -(raw42361step2 i j); unfold raw42361step3 raw42361step2; decide +kernel
      have hl : raw42361step3Labels = raw42361step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42361step3 raw42361step3Labels = mixedMoment B raw42361step4 raw42361step4Labels := by
      have ha : raw42361step4 = raw42361step3 := by apply Matrix.ext; unfold raw42361step4 raw42361step3; decide +kernel
      have hl : raw42361step3Labels = labelEmbedding7 ∘ raw42361step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42361step3 raw42361step3Labels raw42361step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw42362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42362Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42362step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42362step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42362 raw42362Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw42362 raw42362Labels = mixedMoment B raw42362step0 raw42362step0Labels := by
      have hz : ∀ j, raw42362 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42362step0 = (fun i j => raw42362 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42362step0 raw42362; decide +kernel
      have hl : raw42362step0Labels = raw42362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42362 raw42362Labels permutation434 hz
    mixedMoment B raw42362step0 raw42362step0Labels = mixedMoment B raw42362step1 raw42362step1Labels := by
      have ha : raw42362step1 = (fun i j => raw42362step0 (permutation133 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42362step1 raw42362step0; decide +kernel
      have hl : raw42362step1Labels = raw42362step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42362step0 raw42362step0Labels permutation133 permutation4
    mixedMoment B raw42362step1 raw42362step1Labels = mixedMoment B raw42362step2 raw42362step2Labels := by
      have ha : raw42362step2 = raw42362step1 := by apply Matrix.ext; unfold raw42362step2 raw42362step1; decide +kernel
      have hl : raw42362step1Labels = labelEmbedding1 ∘ raw42362step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42362step1 raw42362step1Labels raw42362step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw42363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42363Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42363step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42363step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42363step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42363 raw42363Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw42363 raw42363Labels = mixedMoment B raw42363step0 raw42363step0Labels := by
      have hz : ∀ j, raw42363 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42363step0 = (fun i j => raw42363 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42363step0 raw42363; decide +kernel
      have hl : raw42363step0Labels = raw42363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42363 raw42363Labels permutation434 hz
    mixedMoment B raw42363step0 raw42363step0Labels = mixedMoment B raw42363step1 raw42363step1Labels := by
      have ha : raw42363step1 = (fun i j => raw42363step0 (permutation147 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42363step1 raw42363step0; decide +kernel
      have hl : raw42363step1Labels = raw42363step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42363step0 raw42363step0Labels permutation147 permutation5
    mixedMoment B raw42363step1 raw42363step1Labels = mixedMoment B raw42363step2 raw42363step2Labels := by
      have ha : raw42363step2 = raw42363step1 := by apply Matrix.ext; unfold raw42363step2 raw42363step1; decide +kernel
      have hl : raw42363step1Labels = labelEmbedding9 ∘ raw42363step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42363step1 raw42363step1Labels raw42363step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw42364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42364Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42364step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42364 raw42364Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw42364 raw42364Labels = mixedMoment B raw42364step0 raw42364step0Labels := by
      have hz : ∀ j, raw42364 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42364step0 = (fun i j => raw42364 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42364step0 raw42364; decide +kernel
      have hl : raw42364step0Labels = raw42364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42364 raw42364Labels permutation434 hz
    mixedMoment B raw42364step0 raw42364step0Labels = mixedMoment B raw42364step1 raw42364step1Labels := by
      have ha : raw42364step1 = raw42364step0 := by apply Matrix.ext; unfold raw42364step1 raw42364step0; decide +kernel
      have hl : raw42364step0Labels = labelEmbedding1 ∘ raw42364step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42364step0 raw42364step0Labels raw42364step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3883 node3883Labels := by rfl

def raw42365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42365Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42365step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42365step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42365step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42365step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42365step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42365step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42365 raw42365Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw42365 raw42365Labels = mixedMoment B raw42365step0 raw42365step0Labels := by
      have hz : ∀ j, raw42365 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42365step0 = (fun i j => raw42365 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42365step0 raw42365; decide +kernel
      have hl : raw42365step0Labels = raw42365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42365 raw42365Labels permutation434 hz
    mixedMoment B raw42365step0 raw42365step0Labels = mixedMoment B raw42365step1 raw42365step1Labels := by
      have ha : raw42365step1 = (fun i j => raw42365step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42365step1 raw42365step0; decide +kernel
      have hl : raw42365step1Labels = raw42365step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42365step0 raw42365step0Labels permutation151 permutation3
    mixedMoment B raw42365step1 raw42365step1Labels = mixedMoment B raw42365step2 raw42365step2Labels := by
      have ha : raw42365step2 = -raw42365step1 := by apply Matrix.ext; change ∀ i j, raw42365step2 i j = -(raw42365step1 i j); unfold raw42365step2 raw42365step1; decide +kernel
      have hl : raw42365step2Labels = raw42365step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42365step2 raw42365step2Labels = mixedMoment B raw42365step3 raw42365step3Labels := by
      have ha : raw42365step3 = raw42365step2 := by apply Matrix.ext; unfold raw42365step3 raw42365step2; decide +kernel
      have hl : raw42365step2Labels = labelEmbedding7 ∘ raw42365step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42365step2 raw42365step2Labels raw42365step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw42366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42366Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42366step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42366 raw42366Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw42366 raw42366Labels = mixedMoment B raw42366step0 raw42366step0Labels := by
      have hz : ∀ j, raw42366 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42366step0 = (fun i j => raw42366 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42366step0 raw42366; decide +kernel
      have hl : raw42366step0Labels = raw42366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42366 raw42366Labels permutation434 hz
    mixedMoment B raw42366step0 raw42366step0Labels = mixedMoment B raw42366step1 raw42366step1Labels := by
      have ha : raw42366step1 = raw42366step0 := by apply Matrix.ext; unfold raw42366step1 raw42366step0; decide +kernel
      have hl : raw42366step0Labels = labelEmbedding1 ∘ raw42366step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42366step0 raw42366step0Labels raw42366step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw42367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42367Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42367step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42367step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42367 raw42367Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw42367 raw42367Labels = mixedMoment B raw42367step0 raw42367step0Labels := by
      have hz : ∀ j, raw42367 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42367step0 = (fun i j => raw42367 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42367step0 raw42367; decide +kernel
      have hl : raw42367step0Labels = raw42367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42367 raw42367Labels permutation434 hz
    mixedMoment B raw42367step0 raw42367step0Labels = mixedMoment B raw42367step1 raw42367step1Labels := by
      have ha : raw42367step1 = raw42367step0 := by apply Matrix.ext; unfold raw42367step1 raw42367step0; decide +kernel
      have hl : raw42367step0Labels = labelEmbedding8 ∘ raw42367step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42367step0 raw42367step0Labels raw42367step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
