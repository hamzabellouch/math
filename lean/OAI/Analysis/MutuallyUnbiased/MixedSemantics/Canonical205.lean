import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw26240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26240 raw26240Labels = mixedMoment B node4237 node4237Labels := by
  calc
    mixedMoment B raw26240 raw26240Labels = mixedMoment B raw26240step0 raw26240step0Labels := by
      have hz : ∀ j, raw26240 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26240step0 = (fun i j => raw26240 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26240step0 raw26240; decide +kernel
      have hl : raw26240step0Labels = raw26240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26240 raw26240Labels permutation346 hz
    _ = mixedMoment B node4237 node4237Labels := by rfl

def raw26241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26241 raw26241Labels = mixedMoment B node4199 node4199Labels := by
  calc
    mixedMoment B raw26241 raw26241Labels = mixedMoment B raw26241step0 raw26241step0Labels := by
      have ha : raw26241step0 = (fun i j => raw26241 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26241step0 raw26241; decide +kernel
      have hl : raw26241step0Labels = raw26241Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26241 raw26241Labels permutation176 permutation2
    _ = mixedMoment B node4199 node4199Labels := by rfl

def raw26242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26242 raw26242Labels = mixedMoment B node4253 node4253Labels := by
  calc
    mixedMoment B raw26242 raw26242Labels = mixedMoment B raw26242step0 raw26242step0Labels := by
      have hz : ∀ j, raw26242 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26242step0 = (fun i j => raw26242 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26242step0 raw26242; decide +kernel
      have hl : raw26242step0Labels = raw26242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26242 raw26242Labels permutation346 hz
    _ = mixedMoment B node4253 node4253Labels := by rfl

def raw26243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw26243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw26243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26243 raw26243Labels = mixedMoment B node4253 node4253Labels := by
  calc
    mixedMoment B raw26243 raw26243Labels = mixedMoment B raw26243step0 raw26243step0Labels := by
      have hz : ∀ j, raw26243 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26243step0 = (fun i j => raw26243 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26243step0 raw26243; decide +kernel
      have hl : raw26243step0Labels = raw26243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26243 raw26243Labels permutation346 hz
    mixedMoment B raw26243step0 raw26243step0Labels = mixedMoment B raw26243step1 raw26243step1Labels := by
      have ha : raw26243step1 = (fun i j => raw26243step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26243step1 raw26243step0; decide +kernel
      have hl : raw26243step1Labels = raw26243step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26243step0 raw26243step0Labels permutation34 permutation2
    _ = mixedMoment B node4253 node4253Labels := by rfl

def raw26244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26244Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26244step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26244step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26244step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26244step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26244step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26244step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26244 raw26244Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw26244 raw26244Labels = mixedMoment B raw26244step0 raw26244step0Labels := by
      have hz : ∀ j, raw26244 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26244step0 = (fun i j => raw26244 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26244step0 raw26244; decide +kernel
      have hl : raw26244step0Labels = raw26244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26244 raw26244Labels permutation346 hz
    mixedMoment B raw26244step0 raw26244step0Labels = mixedMoment B raw26244step1 raw26244step1Labels := by
      have ha : raw26244step1 = (fun i j => raw26244step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26244step1 raw26244step0; decide +kernel
      have hl : raw26244step1Labels = raw26244step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26244step0 raw26244step0Labels permutation32 permutation7
    mixedMoment B raw26244step1 raw26244step1Labels = mixedMoment B raw26244step2 raw26244step2Labels := by
      have ha : raw26244step2 = -raw26244step1 := by apply Matrix.ext; change ∀ i j, raw26244step2 i j = -(raw26244step1 i j); unfold raw26244step2 raw26244step1; decide +kernel
      have hl : raw26244step2Labels = raw26244step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26244step2 raw26244step2Labels = mixedMoment B raw26244step3 raw26244step3Labels := by
      have ha : raw26244step3 = raw26244step2 := by apply Matrix.ext; unfold raw26244step3 raw26244step2; decide +kernel
      have hl : raw26244step2Labels = labelEmbedding1 ∘ raw26244step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26244step2 raw26244step2Labels raw26244step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1073 node1073Labels := by rfl

def raw26245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26245Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26245step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26245step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26245step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26245step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26245step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26245step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26245 raw26245Labels = mixedMoment B node998 node998Labels := by
  calc
    mixedMoment B raw26245 raw26245Labels = mixedMoment B raw26245step0 raw26245step0Labels := by
      have ha : raw26245step0 = (fun i j => raw26245 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26245step0 raw26245; decide +kernel
      have hl : raw26245step0Labels = raw26245Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26245 raw26245Labels permutation176 permutation7
    mixedMoment B raw26245step0 raw26245step0Labels = mixedMoment B raw26245step1 raw26245step1Labels := by
      have ha : raw26245step1 = -raw26245step0 := by apply Matrix.ext; change ∀ i j, raw26245step1 i j = -(raw26245step0 i j); unfold raw26245step1 raw26245step0; decide +kernel
      have hl : raw26245step1Labels = raw26245step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26245step1 raw26245step1Labels = mixedMoment B raw26245step2 raw26245step2Labels := by
      have ha : raw26245step2 = raw26245step1 := by apply Matrix.ext; unfold raw26245step2 raw26245step1; decide +kernel
      have hl : raw26245step1Labels = labelEmbedding1 ∘ raw26245step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26245step1 raw26245step1Labels raw26245step2Labels labelEmbedding1 hl
    _ = mixedMoment B node998 node998Labels := by rfl

def raw26246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26246Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26246step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26246step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26246step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26246step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26246step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26246step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26246 raw26246Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw26246 raw26246Labels = mixedMoment B raw26246step0 raw26246step0Labels := by
      have hz : ∀ j, raw26246 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26246step0 = (fun i j => raw26246 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26246step0 raw26246; decide +kernel
      have hl : raw26246step0Labels = raw26246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26246 raw26246Labels permutation346 hz
    mixedMoment B raw26246step0 raw26246step0Labels = mixedMoment B raw26246step1 raw26246step1Labels := by
      have ha : raw26246step1 = (fun i j => raw26246step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26246step1 raw26246step0; decide +kernel
      have hl : raw26246step1Labels = raw26246step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26246step0 raw26246step0Labels permutation32 permutation7
    mixedMoment B raw26246step1 raw26246step1Labels = mixedMoment B raw26246step2 raw26246step2Labels := by
      have ha : raw26246step2 = -raw26246step1 := by apply Matrix.ext; change ∀ i j, raw26246step2 i j = -(raw26246step1 i j); unfold raw26246step2 raw26246step1; decide +kernel
      have hl : raw26246step2Labels = raw26246step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26246step2 raw26246step2Labels = mixedMoment B raw26246step3 raw26246step3Labels := by
      have ha : raw26246step3 = raw26246step2 := by apply Matrix.ext; unfold raw26246step3 raw26246step2; decide +kernel
      have hl : raw26246step2Labels = labelEmbedding1 ∘ raw26246step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26246step2 raw26246step2Labels raw26246step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1079 node1079Labels := by rfl

def raw26247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26247Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26247step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26247step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26247step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26247step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26247step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26247step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26247 raw26247Labels = mixedMoment B node1079 node1079Labels := by
  calc
    mixedMoment B raw26247 raw26247Labels = mixedMoment B raw26247step0 raw26247step0Labels := by
      have hz : ∀ j, raw26247 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26247step0 = (fun i j => raw26247 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26247step0 raw26247; decide +kernel
      have hl : raw26247step0Labels = raw26247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26247 raw26247Labels permutation346 hz
    mixedMoment B raw26247step0 raw26247step0Labels = mixedMoment B raw26247step1 raw26247step1Labels := by
      have ha : raw26247step1 = (fun i j => raw26247step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26247step1 raw26247step0; decide +kernel
      have hl : raw26247step1Labels = raw26247step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26247step0 raw26247step0Labels permutation34 permutation7
    mixedMoment B raw26247step1 raw26247step1Labels = mixedMoment B raw26247step2 raw26247step2Labels := by
      have ha : raw26247step2 = -raw26247step1 := by apply Matrix.ext; change ∀ i j, raw26247step2 i j = -(raw26247step1 i j); unfold raw26247step2 raw26247step1; decide +kernel
      have hl : raw26247step2Labels = raw26247step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26247step2 raw26247step2Labels = mixedMoment B raw26247step3 raw26247step3Labels := by
      have ha : raw26247step3 = raw26247step2 := by apply Matrix.ext; unfold raw26247step3 raw26247step2; decide +kernel
      have hl : raw26247step2Labels = labelEmbedding1 ∘ raw26247step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26247step2 raw26247step2Labels raw26247step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1079 node1079Labels := by rfl

def raw26248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26248Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26248step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26248step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26248step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26248step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26248step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26248step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26248 raw26248Labels = mixedMoment B node1081 node1081Labels := by
  calc
    mixedMoment B raw26248 raw26248Labels = mixedMoment B raw26248step0 raw26248step0Labels := by
      have hz : ∀ j, raw26248 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26248step0 = (fun i j => raw26248 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26248step0 raw26248; decide +kernel
      have hl : raw26248step0Labels = raw26248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26248 raw26248Labels permutation346 hz
    mixedMoment B raw26248step0 raw26248step0Labels = mixedMoment B raw26248step1 raw26248step1Labels := by
      have ha : raw26248step1 = (fun i j => raw26248step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26248step1 raw26248step0; decide +kernel
      have hl : raw26248step1Labels = raw26248step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26248step0 raw26248step0Labels permutation32 permutation7
    mixedMoment B raw26248step1 raw26248step1Labels = mixedMoment B raw26248step2 raw26248step2Labels := by
      have ha : raw26248step2 = -raw26248step1 := by apply Matrix.ext; change ∀ i j, raw26248step2 i j = -(raw26248step1 i j); unfold raw26248step2 raw26248step1; decide +kernel
      have hl : raw26248step2Labels = raw26248step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26248step2 raw26248step2Labels = mixedMoment B raw26248step3 raw26248step3Labels := by
      have ha : raw26248step3 = raw26248step2 := by apply Matrix.ext; unfold raw26248step3 raw26248step2; decide +kernel
      have hl : raw26248step2Labels = labelEmbedding1 ∘ raw26248step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26248step2 raw26248step2Labels raw26248step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1081 node1081Labels := by rfl

def raw26249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26249Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26249step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26249step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26249step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26249step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26249step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26249 raw26249Labels = mixedMoment B node687 node687Labels := by
  calc
    mixedMoment B raw26249 raw26249Labels = mixedMoment B raw26249step0 raw26249step0Labels := by
      have hz : ∀ j, raw26249 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26249step0 = (fun i j => raw26249 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26249step0 raw26249; decide +kernel
      have hl : raw26249step0Labels = raw26249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26249 raw26249Labels permutation346 hz
    mixedMoment B raw26249step0 raw26249step0Labels = mixedMoment B raw26249step1 raw26249step1Labels := by
      have ha : raw26249step1 = (fun i j => raw26249step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26249step1 raw26249step0; decide +kernel
      have hl : raw26249step1Labels = raw26249step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26249step0 raw26249step0Labels permutation32 permutation7
    mixedMoment B raw26249step1 raw26249step1Labels = mixedMoment B raw26249step2 raw26249step2Labels := by
      have ha : raw26249step2 = -raw26249step1 := by apply Matrix.ext; change ∀ i j, raw26249step2 i j = -(raw26249step1 i j); unfold raw26249step2 raw26249step1; decide +kernel
      have hl : raw26249step2Labels = raw26249step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26249step2 raw26249step2Labels = mixedMoment B raw26249step3 raw26249step3Labels := by
      have ha : raw26249step3 = raw26249step2 := by apply Matrix.ext; unfold raw26249step3 raw26249step2; decide +kernel
      have hl : raw26249step2Labels = labelEmbedding1 ∘ raw26249step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26249step2 raw26249step2Labels raw26249step3Labels labelEmbedding1 hl
    _ = mixedMoment B node687 node687Labels := by rfl

def raw26250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26250Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26250step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26250step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26250step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26250step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26250step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26250step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26250 raw26250Labels = mixedMoment B node766 node766Labels := by
  calc
    mixedMoment B raw26250 raw26250Labels = mixedMoment B raw26250step0 raw26250step0Labels := by
      have ha : raw26250step0 = (fun i j => raw26250 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26250step0 raw26250; decide +kernel
      have hl : raw26250step0Labels = raw26250Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26250 raw26250Labels permutation176 permutation7
    mixedMoment B raw26250step0 raw26250step0Labels = mixedMoment B raw26250step1 raw26250step1Labels := by
      have ha : raw26250step1 = -raw26250step0 := by apply Matrix.ext; change ∀ i j, raw26250step1 i j = -(raw26250step0 i j); unfold raw26250step1 raw26250step0; decide +kernel
      have hl : raw26250step1Labels = raw26250step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26250step1 raw26250step1Labels = mixedMoment B raw26250step2 raw26250step2Labels := by
      have ha : raw26250step2 = raw26250step1 := by apply Matrix.ext; unfold raw26250step2 raw26250step1; decide +kernel
      have hl : raw26250step1Labels = labelEmbedding1 ∘ raw26250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26250step1 raw26250step1Labels raw26250step2Labels labelEmbedding1 hl
    _ = mixedMoment B node766 node766Labels := by rfl

def raw26251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26251Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26251step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26251step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26251step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26251step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26251step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26251step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26251step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26251 raw26251Labels = mixedMoment B node850 node850Labels := by
  calc
    mixedMoment B raw26251 raw26251Labels = mixedMoment B raw26251step0 raw26251step0Labels := by
      have hz : ∀ j, raw26251 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26251step0 = (fun i j => raw26251 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26251step0 raw26251; decide +kernel
      have hl : raw26251step0Labels = raw26251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26251 raw26251Labels permutation346 hz
    mixedMoment B raw26251step0 raw26251step0Labels = mixedMoment B raw26251step1 raw26251step1Labels := by
      have ha : raw26251step1 = (fun i j => raw26251step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26251step1 raw26251step0; decide +kernel
      have hl : raw26251step1Labels = raw26251step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26251step0 raw26251step0Labels permutation38 permutation7
    mixedMoment B raw26251step1 raw26251step1Labels = mixedMoment B raw26251step2 raw26251step2Labels := by
      have ha : raw26251step2 = -raw26251step1 := by apply Matrix.ext; change ∀ i j, raw26251step2 i j = -(raw26251step1 i j); unfold raw26251step2 raw26251step1; decide +kernel
      have hl : raw26251step2Labels = raw26251step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26251step2 raw26251step2Labels = mixedMoment B raw26251step3 raw26251step3Labels := by
      have ha : raw26251step3 = raw26251step2 := by apply Matrix.ext; unfold raw26251step3 raw26251step2; decide +kernel
      have hl : raw26251step2Labels = labelEmbedding1 ∘ raw26251step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26251step2 raw26251step2Labels raw26251step3Labels labelEmbedding1 hl
    _ = mixedMoment B node850 node850Labels := by rfl

def raw26252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26252Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26252step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26252step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26252step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26252step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26252step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26252 raw26252Labels = mixedMoment B node850 node850Labels := by
  calc
    mixedMoment B raw26252 raw26252Labels = mixedMoment B raw26252step0 raw26252step0Labels := by
      have hz : ∀ j, raw26252 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26252step0 = (fun i j => raw26252 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26252step0 raw26252; decide +kernel
      have hl : raw26252step0Labels = raw26252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26252 raw26252Labels permutation346 hz
    mixedMoment B raw26252step0 raw26252step0Labels = mixedMoment B raw26252step1 raw26252step1Labels := by
      have ha : raw26252step1 = (fun i j => raw26252step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26252step1 raw26252step0; decide +kernel
      have hl : raw26252step1Labels = raw26252step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26252step0 raw26252step0Labels permutation44 permutation7
    mixedMoment B raw26252step1 raw26252step1Labels = mixedMoment B raw26252step2 raw26252step2Labels := by
      have ha : raw26252step2 = -raw26252step1 := by apply Matrix.ext; change ∀ i j, raw26252step2 i j = -(raw26252step1 i j); unfold raw26252step2 raw26252step1; decide +kernel
      have hl : raw26252step2Labels = raw26252step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26252step2 raw26252step2Labels = mixedMoment B raw26252step3 raw26252step3Labels := by
      have ha : raw26252step3 = raw26252step2 := by apply Matrix.ext; unfold raw26252step3 raw26252step2; decide +kernel
      have hl : raw26252step2Labels = labelEmbedding1 ∘ raw26252step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26252step2 raw26252step2Labels raw26252step3Labels labelEmbedding1 hl
    _ = mixedMoment B node850 node850Labels := by rfl

def raw26253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26253Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26253step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26253step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw26253step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26253 raw26253Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw26253 raw26253Labels = mixedMoment B raw26253step0 raw26253step0Labels := by
      have hz : ∀ j, raw26253 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26253step0 = (fun i j => raw26253 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26253step0 raw26253; decide +kernel
      have hl : raw26253step0Labels = raw26253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26253 raw26253Labels permutation346 hz
    mixedMoment B raw26253step0 raw26253step0Labels = mixedMoment B raw26253step1 raw26253step1Labels := by
      have hz : ∀ i, raw26253step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw26253step1 = (fun i j => raw26253step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw26253step1 raw26253step0; decide +kernel
      have hl : raw26253step1Labels = (fun j => raw26253step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26253step0 raw26253step0Labels permutation4 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

def raw26254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26254Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 1, -5], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26254step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26254step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26254step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, -1, 5], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26254step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26254 raw26254Labels = mixedMoment B node662 node662Labels := by
  calc
    mixedMoment B raw26254 raw26254Labels = mixedMoment B raw26254step0 raw26254step0Labels := by
      have ha : raw26254step0 = (fun i j => raw26254 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26254step0 raw26254; decide +kernel
      have hl : raw26254step0Labels = raw26254Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26254 raw26254Labels permutation176 permutation7
    mixedMoment B raw26254step0 raw26254step0Labels = mixedMoment B raw26254step1 raw26254step1Labels := by
      have ha : raw26254step1 = -raw26254step0 := by apply Matrix.ext; change ∀ i j, raw26254step1 i j = -(raw26254step0 i j); unfold raw26254step1 raw26254step0; decide +kernel
      have hl : raw26254step1Labels = raw26254step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26254step1 raw26254step1Labels = mixedMoment B raw26254step2 raw26254step2Labels := by
      have ha : raw26254step2 = raw26254step1 := by apply Matrix.ext; unfold raw26254step2 raw26254step1; decide +kernel
      have hl : raw26254step1Labels = labelEmbedding1 ∘ raw26254step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26254step1 raw26254step1Labels raw26254step2Labels labelEmbedding1 hl
    _ = mixedMoment B node662 node662Labels := by rfl

def raw26255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26255Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26255step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26255step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26255step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26255step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26255step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26255 raw26255Labels = mixedMoment B node798 node798Labels := by
  calc
    mixedMoment B raw26255 raw26255Labels = mixedMoment B raw26255step0 raw26255step0Labels := by
      have ha : raw26255step0 = (fun i j => raw26255 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26255step0 raw26255; decide +kernel
      have hl : raw26255step0Labels = raw26255Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26255 raw26255Labels permutation176 permutation7
    mixedMoment B raw26255step0 raw26255step0Labels = mixedMoment B raw26255step1 raw26255step1Labels := by
      have ha : raw26255step1 = -raw26255step0 := by apply Matrix.ext; change ∀ i j, raw26255step1 i j = -(raw26255step0 i j); unfold raw26255step1 raw26255step0; decide +kernel
      have hl : raw26255step1Labels = raw26255step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26255step1 raw26255step1Labels = mixedMoment B raw26255step2 raw26255step2Labels := by
      have ha : raw26255step2 = raw26255step1 := by apply Matrix.ext; unfold raw26255step2 raw26255step1; decide +kernel
      have hl : raw26255step1Labels = labelEmbedding1 ∘ raw26255step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26255step1 raw26255step1Labels raw26255step2Labels labelEmbedding1 hl
    _ = mixedMoment B node798 node798Labels := by rfl

def raw26256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26256Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26256step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26256step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26256step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26256step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26256step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26256 raw26256Labels = mixedMoment B node803 node803Labels := by
  calc
    mixedMoment B raw26256 raw26256Labels = mixedMoment B raw26256step0 raw26256step0Labels := by
      have ha : raw26256step0 = (fun i j => raw26256 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26256step0 raw26256; decide +kernel
      have hl : raw26256step0Labels = raw26256Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26256 raw26256Labels permutation176 permutation7
    mixedMoment B raw26256step0 raw26256step0Labels = mixedMoment B raw26256step1 raw26256step1Labels := by
      have ha : raw26256step1 = -raw26256step0 := by apply Matrix.ext; change ∀ i j, raw26256step1 i j = -(raw26256step0 i j); unfold raw26256step1 raw26256step0; decide +kernel
      have hl : raw26256step1Labels = raw26256step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26256step1 raw26256step1Labels = mixedMoment B raw26256step2 raw26256step2Labels := by
      have ha : raw26256step2 = raw26256step1 := by apply Matrix.ext; unfold raw26256step2 raw26256step1; decide +kernel
      have hl : raw26256step1Labels = labelEmbedding1 ∘ raw26256step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26256step1 raw26256step1Labels raw26256step2Labels labelEmbedding1 hl
    _ = mixedMoment B node803 node803Labels := by rfl

def raw26257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26257Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw26257step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26257step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26257step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26257step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw26257step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26257 raw26257Labels = mixedMoment B node803 node803Labels := by
  calc
    mixedMoment B raw26257 raw26257Labels = mixedMoment B raw26257step0 raw26257step0Labels := by
      have ha : raw26257step0 = (fun i j => raw26257 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26257step0 raw26257; decide +kernel
      have hl : raw26257step0Labels = raw26257Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26257 raw26257Labels permutation178 permutation7
    mixedMoment B raw26257step0 raw26257step0Labels = mixedMoment B raw26257step1 raw26257step1Labels := by
      have ha : raw26257step1 = -raw26257step0 := by apply Matrix.ext; change ∀ i j, raw26257step1 i j = -(raw26257step0 i j); unfold raw26257step1 raw26257step0; decide +kernel
      have hl : raw26257step1Labels = raw26257step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26257step1 raw26257step1Labels = mixedMoment B raw26257step2 raw26257step2Labels := by
      have ha : raw26257step2 = raw26257step1 := by apply Matrix.ext; unfold raw26257step2 raw26257step1; decide +kernel
      have hl : raw26257step1Labels = labelEmbedding1 ∘ raw26257step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26257step1 raw26257step1Labels raw26257step2Labels labelEmbedding1 hl
    _ = mixedMoment B node803 node803Labels := by rfl

def raw26258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26258Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw26258step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26258step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26258step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26258step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26258 raw26258Labels = mixedMoment B node805 node805Labels := by
  calc
    mixedMoment B raw26258 raw26258Labels = mixedMoment B raw26258step0 raw26258step0Labels := by
      have ha : raw26258step0 = (fun i j => raw26258 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26258step0 raw26258; decide +kernel
      have hl : raw26258step0Labels = raw26258Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26258 raw26258Labels permutation176 permutation7
    mixedMoment B raw26258step0 raw26258step0Labels = mixedMoment B raw26258step1 raw26258step1Labels := by
      have ha : raw26258step1 = -raw26258step0 := by apply Matrix.ext; change ∀ i j, raw26258step1 i j = -(raw26258step0 i j); unfold raw26258step1 raw26258step0; decide +kernel
      have hl : raw26258step1Labels = raw26258step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26258step1 raw26258step1Labels = mixedMoment B raw26258step2 raw26258step2Labels := by
      have ha : raw26258step2 = raw26258step1 := by apply Matrix.ext; unfold raw26258step2 raw26258step1; decide +kernel
      have hl : raw26258step1Labels = labelEmbedding1 ∘ raw26258step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26258step1 raw26258step1Labels raw26258step2Labels labelEmbedding1 hl
    _ = mixedMoment B node805 node805Labels := by rfl

def raw26259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26259Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26259step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw26259step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26259step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26259step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26259step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26259step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26259 raw26259Labels = mixedMoment B node682 node682Labels := by
  calc
    mixedMoment B raw26259 raw26259Labels = mixedMoment B raw26259step0 raw26259step0Labels := by
      have hz : ∀ j, raw26259 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26259step0 = (fun i j => raw26259 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26259step0 raw26259; decide +kernel
      have hl : raw26259step0Labels = raw26259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26259 raw26259Labels permutation346 hz
    mixedMoment B raw26259step0 raw26259step0Labels = mixedMoment B raw26259step1 raw26259step1Labels := by
      have ha : raw26259step1 = (fun i j => raw26259step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26259step1 raw26259step0; decide +kernel
      have hl : raw26259step1Labels = raw26259step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26259step0 raw26259step0Labels permutation34 permutation7
    mixedMoment B raw26259step1 raw26259step1Labels = mixedMoment B raw26259step2 raw26259step2Labels := by
      have ha : raw26259step2 = -raw26259step1 := by apply Matrix.ext; change ∀ i j, raw26259step2 i j = -(raw26259step1 i j); unfold raw26259step2 raw26259step1; decide +kernel
      have hl : raw26259step2Labels = raw26259step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26259step2 raw26259step2Labels = mixedMoment B raw26259step3 raw26259step3Labels := by
      have ha : raw26259step3 = raw26259step2 := by apply Matrix.ext; unfold raw26259step3 raw26259step2; decide +kernel
      have hl : raw26259step2Labels = labelEmbedding1 ∘ raw26259step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26259step2 raw26259step2Labels raw26259step3Labels labelEmbedding1 hl
    _ = mixedMoment B node682 node682Labels := by rfl

def raw26260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26260Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26260step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw26260step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26260step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26260step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26260step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26260step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26260 raw26260Labels = mixedMoment B node841 node841Labels := by
  calc
    mixedMoment B raw26260 raw26260Labels = mixedMoment B raw26260step0 raw26260step0Labels := by
      have hz : ∀ j, raw26260 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26260step0 = (fun i j => raw26260 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26260step0 raw26260; decide +kernel
      have hl : raw26260step0Labels = raw26260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26260 raw26260Labels permutation346 hz
    mixedMoment B raw26260step0 raw26260step0Labels = mixedMoment B raw26260step1 raw26260step1Labels := by
      have ha : raw26260step1 = (fun i j => raw26260step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26260step1 raw26260step0; decide +kernel
      have hl : raw26260step1Labels = raw26260step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26260step0 raw26260step0Labels permutation34 permutation7
    mixedMoment B raw26260step1 raw26260step1Labels = mixedMoment B raw26260step2 raw26260step2Labels := by
      have ha : raw26260step2 = -raw26260step1 := by apply Matrix.ext; change ∀ i j, raw26260step2 i j = -(raw26260step1 i j); unfold raw26260step2 raw26260step1; decide +kernel
      have hl : raw26260step2Labels = raw26260step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26260step2 raw26260step2Labels = mixedMoment B raw26260step3 raw26260step3Labels := by
      have ha : raw26260step3 = raw26260step2 := by apply Matrix.ext; unfold raw26260step3 raw26260step2; decide +kernel
      have hl : raw26260step2Labels = labelEmbedding1 ∘ raw26260step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26260step2 raw26260step2Labels raw26260step3Labels labelEmbedding1 hl
    _ = mixedMoment B node841 node841Labels := by rfl

def raw26261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26261Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw26261step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26261step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26261step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26261step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26261step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26261 raw26261Labels = mixedMoment B node761 node761Labels := by
  calc
    mixedMoment B raw26261 raw26261Labels = mixedMoment B raw26261step0 raw26261step0Labels := by
      have ha : raw26261step0 = (fun i j => raw26261 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26261step0 raw26261; decide +kernel
      have hl : raw26261step0Labels = raw26261Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26261 raw26261Labels permutation178 permutation7
    mixedMoment B raw26261step0 raw26261step0Labels = mixedMoment B raw26261step1 raw26261step1Labels := by
      have ha : raw26261step1 = -raw26261step0 := by apply Matrix.ext; change ∀ i j, raw26261step1 i j = -(raw26261step0 i j); unfold raw26261step1 raw26261step0; decide +kernel
      have hl : raw26261step1Labels = raw26261step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26261step1 raw26261step1Labels = mixedMoment B raw26261step2 raw26261step2Labels := by
      have ha : raw26261step2 = raw26261step1 := by apply Matrix.ext; unfold raw26261step2 raw26261step1; decide +kernel
      have hl : raw26261step1Labels = labelEmbedding1 ∘ raw26261step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26261step1 raw26261step1Labels raw26261step2Labels labelEmbedding1 hl
    _ = mixedMoment B node761 node761Labels := by rfl

def raw26262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26262Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw26262step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw26262step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw26262step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26262step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw26262step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26262 raw26262Labels = mixedMoment B node848 node848Labels := by
  calc
    mixedMoment B raw26262 raw26262Labels = mixedMoment B raw26262step0 raw26262step0Labels := by
      have hz : ∀ j, raw26262 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26262step0 = (fun i j => raw26262 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26262step0 raw26262; decide +kernel
      have hl : raw26262step0Labels = raw26262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26262 raw26262Labels permutation346 hz
    mixedMoment B raw26262step0 raw26262step0Labels = mixedMoment B raw26262step1 raw26262step1Labels := by
      have ha : raw26262step1 = (fun i j => raw26262step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26262step1 raw26262step0; decide +kernel
      have hl : raw26262step1Labels = raw26262step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26262step0 raw26262step0Labels permutation34 permutation7
    mixedMoment B raw26262step1 raw26262step1Labels = mixedMoment B raw26262step2 raw26262step2Labels := by
      have ha : raw26262step2 = -raw26262step1 := by apply Matrix.ext; change ∀ i j, raw26262step2 i j = -(raw26262step1 i j); unfold raw26262step2 raw26262step1; decide +kernel
      have hl : raw26262step2Labels = raw26262step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26262step2 raw26262step2Labels = mixedMoment B raw26262step3 raw26262step3Labels := by
      have ha : raw26262step3 = raw26262step2 := by apply Matrix.ext; unfold raw26262step3 raw26262step2; decide +kernel
      have hl : raw26262step2Labels = labelEmbedding1 ∘ raw26262step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26262step2 raw26262step2Labels raw26262step3Labels labelEmbedding1 hl
    _ = mixedMoment B node848 node848Labels := by rfl

def raw26263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26263Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw26263step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26263step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26263step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26263step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26263step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26263step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26263 raw26263Labels = mixedMoment B node850 node850Labels := by
  calc
    mixedMoment B raw26263 raw26263Labels = mixedMoment B raw26263step0 raw26263step0Labels := by
      have hz : ∀ j, raw26263 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26263step0 = (fun i j => raw26263 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26263step0 raw26263; decide +kernel
      have hl : raw26263step0Labels = raw26263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26263 raw26263Labels permutation346 hz
    mixedMoment B raw26263step0 raw26263step0Labels = mixedMoment B raw26263step1 raw26263step1Labels := by
      have ha : raw26263step1 = (fun i j => raw26263step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26263step1 raw26263step0; decide +kernel
      have hl : raw26263step1Labels = raw26263step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26263step0 raw26263step0Labels permutation35 permutation7
    mixedMoment B raw26263step1 raw26263step1Labels = mixedMoment B raw26263step2 raw26263step2Labels := by
      have ha : raw26263step2 = -raw26263step1 := by apply Matrix.ext; change ∀ i j, raw26263step2 i j = -(raw26263step1 i j); unfold raw26263step2 raw26263step1; decide +kernel
      have hl : raw26263step2Labels = raw26263step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26263step2 raw26263step2Labels = mixedMoment B raw26263step3 raw26263step3Labels := by
      have ha : raw26263step3 = raw26263step2 := by apply Matrix.ext; unfold raw26263step3 raw26263step2; decide +kernel
      have hl : raw26263step2Labels = labelEmbedding1 ∘ raw26263step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26263step2 raw26263step2Labels raw26263step3Labels labelEmbedding1 hl
    _ = mixedMoment B node850 node850Labels := by rfl

def raw26264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26264Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26264step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw26264step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26264step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26264step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26264step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26264step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26264 raw26264Labels = mixedMoment B node682 node682Labels := by
  calc
    mixedMoment B raw26264 raw26264Labels = mixedMoment B raw26264step0 raw26264step0Labels := by
      have hz : ∀ j, raw26264 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26264step0 = (fun i j => raw26264 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26264step0 raw26264; decide +kernel
      have hl : raw26264step0Labels = raw26264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26264 raw26264Labels permutation346 hz
    mixedMoment B raw26264step0 raw26264step0Labels = mixedMoment B raw26264step1 raw26264step1Labels := by
      have ha : raw26264step1 = (fun i j => raw26264step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26264step1 raw26264step0; decide +kernel
      have hl : raw26264step1Labels = raw26264step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26264step0 raw26264step0Labels permutation32 permutation7
    mixedMoment B raw26264step1 raw26264step1Labels = mixedMoment B raw26264step2 raw26264step2Labels := by
      have ha : raw26264step2 = -raw26264step1 := by apply Matrix.ext; change ∀ i j, raw26264step2 i j = -(raw26264step1 i j); unfold raw26264step2 raw26264step1; decide +kernel
      have hl : raw26264step2Labels = raw26264step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26264step2 raw26264step2Labels = mixedMoment B raw26264step3 raw26264step3Labels := by
      have ha : raw26264step3 = raw26264step2 := by apply Matrix.ext; unfold raw26264step3 raw26264step2; decide +kernel
      have hl : raw26264step2Labels = labelEmbedding1 ∘ raw26264step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26264step2 raw26264step2Labels raw26264step3Labels labelEmbedding1 hl
    _ = mixedMoment B node682 node682Labels := by rfl

def raw26265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26265Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26265step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw26265step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26265step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26265step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26265step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26265step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26265 raw26265Labels = mixedMoment B node841 node841Labels := by
  calc
    mixedMoment B raw26265 raw26265Labels = mixedMoment B raw26265step0 raw26265step0Labels := by
      have hz : ∀ j, raw26265 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26265step0 = (fun i j => raw26265 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26265step0 raw26265; decide +kernel
      have hl : raw26265step0Labels = raw26265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26265 raw26265Labels permutation346 hz
    mixedMoment B raw26265step0 raw26265step0Labels = mixedMoment B raw26265step1 raw26265step1Labels := by
      have ha : raw26265step1 = (fun i j => raw26265step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26265step1 raw26265step0; decide +kernel
      have hl : raw26265step1Labels = raw26265step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26265step0 raw26265step0Labels permutation32 permutation7
    mixedMoment B raw26265step1 raw26265step1Labels = mixedMoment B raw26265step2 raw26265step2Labels := by
      have ha : raw26265step2 = -raw26265step1 := by apply Matrix.ext; change ∀ i j, raw26265step2 i j = -(raw26265step1 i j); unfold raw26265step2 raw26265step1; decide +kernel
      have hl : raw26265step2Labels = raw26265step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26265step2 raw26265step2Labels = mixedMoment B raw26265step3 raw26265step3Labels := by
      have ha : raw26265step3 = raw26265step2 := by apply Matrix.ext; unfold raw26265step3 raw26265step2; decide +kernel
      have hl : raw26265step2Labels = labelEmbedding1 ∘ raw26265step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26265step2 raw26265step2Labels raw26265step3Labels labelEmbedding1 hl
    _ = mixedMoment B node841 node841Labels := by rfl

def raw26266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26266Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw26266step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26266step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26266step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26266step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw26266step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26266 raw26266Labels = mixedMoment B node761 node761Labels := by
  calc
    mixedMoment B raw26266 raw26266Labels = mixedMoment B raw26266step0 raw26266step0Labels := by
      have ha : raw26266step0 = (fun i j => raw26266 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26266step0 raw26266; decide +kernel
      have hl : raw26266step0Labels = raw26266Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26266 raw26266Labels permutation176 permutation7
    mixedMoment B raw26266step0 raw26266step0Labels = mixedMoment B raw26266step1 raw26266step1Labels := by
      have ha : raw26266step1 = -raw26266step0 := by apply Matrix.ext; change ∀ i j, raw26266step1 i j = -(raw26266step0 i j); unfold raw26266step1 raw26266step0; decide +kernel
      have hl : raw26266step1Labels = raw26266step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26266step1 raw26266step1Labels = mixedMoment B raw26266step2 raw26266step2Labels := by
      have ha : raw26266step2 = raw26266step1 := by apply Matrix.ext; unfold raw26266step2 raw26266step1; decide +kernel
      have hl : raw26266step1Labels = labelEmbedding1 ∘ raw26266step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26266step1 raw26266step1Labels raw26266step2Labels labelEmbedding1 hl
    _ = mixedMoment B node761 node761Labels := by rfl

def raw26267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26267Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26267step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw26267step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw26267step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26267step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw26267step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26267 raw26267Labels = mixedMoment B node848 node848Labels := by
  calc
    mixedMoment B raw26267 raw26267Labels = mixedMoment B raw26267step0 raw26267step0Labels := by
      have hz : ∀ j, raw26267 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26267step0 = (fun i j => raw26267 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26267step0 raw26267; decide +kernel
      have hl : raw26267step0Labels = raw26267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26267 raw26267Labels permutation346 hz
    mixedMoment B raw26267step0 raw26267step0Labels = mixedMoment B raw26267step1 raw26267step1Labels := by
      have ha : raw26267step1 = (fun i j => raw26267step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26267step1 raw26267step0; decide +kernel
      have hl : raw26267step1Labels = raw26267step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26267step0 raw26267step0Labels permutation32 permutation7
    mixedMoment B raw26267step1 raw26267step1Labels = mixedMoment B raw26267step2 raw26267step2Labels := by
      have ha : raw26267step2 = -raw26267step1 := by apply Matrix.ext; change ∀ i j, raw26267step2 i j = -(raw26267step1 i j); unfold raw26267step2 raw26267step1; decide +kernel
      have hl : raw26267step2Labels = raw26267step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26267step2 raw26267step2Labels = mixedMoment B raw26267step3 raw26267step3Labels := by
      have ha : raw26267step3 = raw26267step2 := by apply Matrix.ext; unfold raw26267step3 raw26267step2; decide +kernel
      have hl : raw26267step2Labels = labelEmbedding1 ∘ raw26267step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26267step2 raw26267step2Labels raw26267step3Labels labelEmbedding1 hl
    _ = mixedMoment B node848 node848Labels := by rfl

def raw26268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw26268Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw26268step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26268step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26268step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26268step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26268step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26268 raw26268Labels = mixedMoment B node850 node850Labels := by
  calc
    mixedMoment B raw26268 raw26268Labels = mixedMoment B raw26268step0 raw26268step0Labels := by
      have hz : ∀ j, raw26268 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26268step0 = (fun i j => raw26268 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26268step0 raw26268; decide +kernel
      have hl : raw26268step0Labels = raw26268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26268 raw26268Labels permutation346 hz
    mixedMoment B raw26268step0 raw26268step0Labels = mixedMoment B raw26268step1 raw26268step1Labels := by
      have ha : raw26268step1 = (fun i j => raw26268step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26268step1 raw26268step0; decide +kernel
      have hl : raw26268step1Labels = raw26268step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26268step0 raw26268step0Labels permutation33 permutation7
    mixedMoment B raw26268step1 raw26268step1Labels = mixedMoment B raw26268step2 raw26268step2Labels := by
      have ha : raw26268step2 = -raw26268step1 := by apply Matrix.ext; change ∀ i j, raw26268step2 i j = -(raw26268step1 i j); unfold raw26268step2 raw26268step1; decide +kernel
      have hl : raw26268step2Labels = raw26268step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26268step2 raw26268step2Labels = mixedMoment B raw26268step3 raw26268step3Labels := by
      have ha : raw26268step3 = raw26268step2 := by apply Matrix.ext; unfold raw26268step3 raw26268step2; decide +kernel
      have hl : raw26268step2Labels = labelEmbedding1 ∘ raw26268step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26268step2 raw26268step2Labels raw26268step3Labels labelEmbedding1 hl
    _ = mixedMoment B node850 node850Labels := by rfl

def raw26269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26269Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26269step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26269step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 1, -5], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw26269step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26269step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw26269step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26269step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, -1, 5], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw26269step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26269 raw26269Labels = mixedMoment B node681 node681Labels := by
  calc
    mixedMoment B raw26269 raw26269Labels = mixedMoment B raw26269step0 raw26269step0Labels := by
      have hz : ∀ j, raw26269 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26269step0 = (fun i j => raw26269 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26269step0 raw26269; decide +kernel
      have hl : raw26269step0Labels = raw26269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26269 raw26269Labels permutation346 hz
    mixedMoment B raw26269step0 raw26269step0Labels = mixedMoment B raw26269step1 raw26269step1Labels := by
      have ha : raw26269step1 = (fun i j => raw26269step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26269step1 raw26269step0; decide +kernel
      have hl : raw26269step1Labels = raw26269step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26269step0 raw26269step0Labels permutation32 permutation7
    mixedMoment B raw26269step1 raw26269step1Labels = mixedMoment B raw26269step2 raw26269step2Labels := by
      have ha : raw26269step2 = -raw26269step1 := by apply Matrix.ext; change ∀ i j, raw26269step2 i j = -(raw26269step1 i j); unfold raw26269step2 raw26269step1; decide +kernel
      have hl : raw26269step2Labels = raw26269step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26269step2 raw26269step2Labels = mixedMoment B raw26269step3 raw26269step3Labels := by
      have ha : raw26269step3 = raw26269step2 := by apply Matrix.ext; unfold raw26269step3 raw26269step2; decide +kernel
      have hl : raw26269step2Labels = labelEmbedding1 ∘ raw26269step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26269step2 raw26269step2Labels raw26269step3Labels labelEmbedding1 hl
    _ = mixedMoment B node681 node681Labels := by rfl

def raw26270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26270Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26270step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw26270step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26270step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw26270step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26270step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw26270step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26270 raw26270Labels = mixedMoment B node840 node840Labels := by
  calc
    mixedMoment B raw26270 raw26270Labels = mixedMoment B raw26270step0 raw26270step0Labels := by
      have hz : ∀ j, raw26270 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26270step0 = (fun i j => raw26270 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26270step0 raw26270; decide +kernel
      have hl : raw26270step0Labels = raw26270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26270 raw26270Labels permutation346 hz
    mixedMoment B raw26270step0 raw26270step0Labels = mixedMoment B raw26270step1 raw26270step1Labels := by
      have ha : raw26270step1 = (fun i j => raw26270step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26270step1 raw26270step0; decide +kernel
      have hl : raw26270step1Labels = raw26270step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26270step0 raw26270step0Labels permutation32 permutation7
    mixedMoment B raw26270step1 raw26270step1Labels = mixedMoment B raw26270step2 raw26270step2Labels := by
      have ha : raw26270step2 = -raw26270step1 := by apply Matrix.ext; change ∀ i j, raw26270step2 i j = -(raw26270step1 i j); unfold raw26270step2 raw26270step1; decide +kernel
      have hl : raw26270step2Labels = raw26270step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26270step2 raw26270step2Labels = mixedMoment B raw26270step3 raw26270step3Labels := by
      have ha : raw26270step3 = raw26270step2 := by apply Matrix.ext; unfold raw26270step3 raw26270step2; decide +kernel
      have hl : raw26270step2Labels = labelEmbedding1 ∘ raw26270step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26270step2 raw26270step2Labels raw26270step3Labels labelEmbedding1 hl
    _ = mixedMoment B node840 node840Labels := by rfl

def raw26271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26271Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw26271step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26271step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw26271step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26271step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw26271step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26271 raw26271Labels = mixedMoment B node760 node760Labels := by
  calc
    mixedMoment B raw26271 raw26271Labels = mixedMoment B raw26271step0 raw26271step0Labels := by
      have ha : raw26271step0 = (fun i j => raw26271 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26271step0 raw26271; decide +kernel
      have hl : raw26271step0Labels = raw26271Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26271 raw26271Labels permutation176 permutation7
    mixedMoment B raw26271step0 raw26271step0Labels = mixedMoment B raw26271step1 raw26271step1Labels := by
      have ha : raw26271step1 = -raw26271step0 := by apply Matrix.ext; change ∀ i j, raw26271step1 i j = -(raw26271step0 i j); unfold raw26271step1 raw26271step0; decide +kernel
      have hl : raw26271step1Labels = raw26271step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26271step1 raw26271step1Labels = mixedMoment B raw26271step2 raw26271step2Labels := by
      have ha : raw26271step2 = raw26271step1 := by apply Matrix.ext; unfold raw26271step2 raw26271step1; decide +kernel
      have hl : raw26271step1Labels = labelEmbedding1 ∘ raw26271step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26271step1 raw26271step1Labels raw26271step2Labels labelEmbedding1 hl
    _ = mixedMoment B node760 node760Labels := by rfl

def raw26272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26272Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26272step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw26272step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw26272step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26272step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw26272step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26272 raw26272Labels = mixedMoment B node847 node847Labels := by
  calc
    mixedMoment B raw26272 raw26272Labels = mixedMoment B raw26272step0 raw26272step0Labels := by
      have hz : ∀ j, raw26272 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26272step0 = (fun i j => raw26272 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26272step0 raw26272; decide +kernel
      have hl : raw26272step0Labels = raw26272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26272 raw26272Labels permutation346 hz
    mixedMoment B raw26272step0 raw26272step0Labels = mixedMoment B raw26272step1 raw26272step1Labels := by
      have ha : raw26272step1 = (fun i j => raw26272step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26272step1 raw26272step0; decide +kernel
      have hl : raw26272step1Labels = raw26272step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26272step0 raw26272step0Labels permutation32 permutation7
    mixedMoment B raw26272step1 raw26272step1Labels = mixedMoment B raw26272step2 raw26272step2Labels := by
      have ha : raw26272step2 = -raw26272step1 := by apply Matrix.ext; change ∀ i j, raw26272step2 i j = -(raw26272step1 i j); unfold raw26272step2 raw26272step1; decide +kernel
      have hl : raw26272step2Labels = raw26272step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26272step2 raw26272step2Labels = mixedMoment B raw26272step3 raw26272step3Labels := by
      have ha : raw26272step3 = raw26272step2 := by apply Matrix.ext; unfold raw26272step3 raw26272step2; decide +kernel
      have hl : raw26272step2Labels = labelEmbedding1 ∘ raw26272step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26272step2 raw26272step2Labels raw26272step3Labels labelEmbedding1 hl
    _ = mixedMoment B node847 node847Labels := by rfl

def raw26273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw26273Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw26273step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw26273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw26273step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw26273step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw26273step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw26273step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26273 raw26273Labels = mixedMoment B node847 node847Labels := by
  calc
    mixedMoment B raw26273 raw26273Labels = mixedMoment B raw26273step0 raw26273step0Labels := by
      have hz : ∀ j, raw26273 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26273step0 = (fun i j => raw26273 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26273step0 raw26273; decide +kernel
      have hl : raw26273step0Labels = raw26273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26273 raw26273Labels permutation346 hz
    mixedMoment B raw26273step0 raw26273step0Labels = mixedMoment B raw26273step1 raw26273step1Labels := by
      have ha : raw26273step1 = (fun i j => raw26273step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26273step1 raw26273step0; decide +kernel
      have hl : raw26273step1Labels = raw26273step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26273step0 raw26273step0Labels permutation34 permutation7
    mixedMoment B raw26273step1 raw26273step1Labels = mixedMoment B raw26273step2 raw26273step2Labels := by
      have ha : raw26273step2 = -raw26273step1 := by apply Matrix.ext; change ∀ i j, raw26273step2 i j = -(raw26273step1 i j); unfold raw26273step2 raw26273step1; decide +kernel
      have hl : raw26273step2Labels = raw26273step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26273step2 raw26273step2Labels = mixedMoment B raw26273step3 raw26273step3Labels := by
      have ha : raw26273step3 = raw26273step2 := by apply Matrix.ext; unfold raw26273step3 raw26273step2; decide +kernel
      have hl : raw26273step2Labels = labelEmbedding1 ∘ raw26273step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26273step2 raw26273step2Labels raw26273step3Labels labelEmbedding1 hl
    _ = mixedMoment B node847 node847Labels := by rfl

def raw26274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26274Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26274step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26274 raw26274Labels = mixedMoment B node1648 node1648Labels := by
  calc
    mixedMoment B raw26274 raw26274Labels = mixedMoment B raw26274step0 raw26274step0Labels := by
      have hz : ∀ j, raw26274 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26274step0 = (fun i j => raw26274 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26274step0 raw26274; decide +kernel
      have hl : raw26274step0Labels = raw26274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26274 raw26274Labels permutation346 hz
    _ = mixedMoment B node1648 node1648Labels := by rfl

def raw26275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26275Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26275step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26275 raw26275Labels = mixedMoment B node810 node810Labels := by
  calc
    mixedMoment B raw26275 raw26275Labels = mixedMoment B raw26275step0 raw26275step0Labels := by
      have hz : ∀ j, raw26275 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26275step0 = (fun i j => raw26275 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26275step0 raw26275; decide +kernel
      have hl : raw26275step0Labels = raw26275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26275 raw26275Labels permutation346 hz
    _ = mixedMoment B node810 node810Labels := by rfl

def raw26276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26276Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26276 raw26276Labels = mixedMoment B node732 node732Labels := by
  calc
    _ = mixedMoment B node732 node732Labels := by rfl

def raw26277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26277Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26277step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26277step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26277 raw26277Labels = mixedMoment B node739 node739Labels := by
  calc
    mixedMoment B raw26277 raw26277Labels = mixedMoment B raw26277step0 raw26277step0Labels := by
      have hz : ∀ j, raw26277 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26277step0 = (fun i j => raw26277 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26277step0 raw26277; decide +kernel
      have hl : raw26277step0Labels = raw26277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26277 raw26277Labels permutation346 hz
    mixedMoment B raw26277step0 raw26277step0Labels = mixedMoment B raw26277step1 raw26277step1Labels := by
      have ha : raw26277step1 = (fun i j => raw26277step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26277step1 raw26277step0; decide +kernel
      have hl : raw26277step1Labels = raw26277step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26277step0 raw26277step0Labels permutation34 permutation2
    _ = mixedMoment B node739 node739Labels := by rfl

def raw26278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26278Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw26278step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26278 raw26278Labels = mixedMoment B node739 node739Labels := by
  calc
    mixedMoment B raw26278 raw26278Labels = mixedMoment B raw26278step0 raw26278step0Labels := by
      have hz : ∀ j, raw26278 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26278step0 = (fun i j => raw26278 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26278step0 raw26278; decide +kernel
      have hl : raw26278step0Labels = raw26278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26278 raw26278Labels permutation346 hz
    _ = mixedMoment B node739 node739Labels := by rfl

def raw26279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26279Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw26279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26279 raw26279Labels = mixedMoment B node737 node737Labels := by
  calc
    mixedMoment B raw26279 raw26279Labels = mixedMoment B raw26279step0 raw26279step0Labels := by
      have hz : ∀ j, raw26279 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26279step0 = (fun i j => raw26279 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26279step0 raw26279; decide +kernel
      have hl : raw26279step0Labels = raw26279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26279 raw26279Labels permutation346 hz
    _ = mixedMoment B node737 node737Labels := by rfl

def raw26280 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![0, 0], ![1, -1], ![1, -1], ![1, -1]]
def raw26280Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26280step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw26280step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26280 raw26280Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw26280 raw26280Labels = mixedMoment B raw26280step0 raw26280step0Labels := by
      have hz : ∀ j, raw26280 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26280step0 = (fun i j => raw26280 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26280step0 raw26280; decide +kernel
      have hl : raw26280step0Labels = raw26280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26280 raw26280Labels permutation346 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

def raw26281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw26281step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26281step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26281step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26281step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26281step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26281 raw26281Labels = mixedMoment B node4126 node4126Labels := by
  calc
    mixedMoment B raw26281 raw26281Labels = mixedMoment B raw26281step0 raw26281step0Labels := by
      have hz : ∀ j, raw26281 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26281step0 = (fun i j => raw26281 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26281step0 raw26281; decide +kernel
      have hl : raw26281step0Labels = raw26281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26281 raw26281Labels permutation346 hz
    mixedMoment B raw26281step0 raw26281step0Labels = mixedMoment B raw26281step1 raw26281step1Labels := by
      have ha : raw26281step1 = (fun i j => raw26281step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26281step1 raw26281step0; decide +kernel
      have hl : raw26281step1Labels = raw26281step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26281step0 raw26281step0Labels permutation41 permutation4
    mixedMoment B raw26281step1 raw26281step1Labels = mixedMoment B raw26281step2 raw26281step2Labels := by
      have ha : raw26281step2 = -raw26281step1 := by apply Matrix.ext; change ∀ i j, raw26281step2 i j = -(raw26281step1 i j); unfold raw26281step2 raw26281step1; decide +kernel
      have hl : raw26281step2Labels = raw26281step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26281step2 raw26281step2Labels = mixedMoment B raw26281step3 raw26281step3Labels := by
      have ha : raw26281step3 = raw26281step2 := by apply Matrix.ext; unfold raw26281step3 raw26281step2; decide +kernel
      have hl : raw26281step2Labels = labelEmbedding7 ∘ raw26281step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26281step2 raw26281step2Labels raw26281step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4126 node4126Labels := by rfl

def raw26282 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw26282step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26282step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26282step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26282step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26282step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26282 raw26282Labels = mixedMoment B node4217 node4217Labels := by
  calc
    mixedMoment B raw26282 raw26282Labels = mixedMoment B raw26282step0 raw26282step0Labels := by
      have ha : raw26282step0 = (fun i j => raw26282 (permutation185 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26282step0 raw26282; decide +kernel
      have hl : raw26282step0Labels = raw26282Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26282 raw26282Labels permutation185 permutation4
    mixedMoment B raw26282step0 raw26282step0Labels = mixedMoment B raw26282step1 raw26282step1Labels := by
      have ha : raw26282step1 = -raw26282step0 := by apply Matrix.ext; change ∀ i j, raw26282step1 i j = -(raw26282step0 i j); unfold raw26282step1 raw26282step0; decide +kernel
      have hl : raw26282step1Labels = raw26282step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26282step1 raw26282step1Labels = mixedMoment B raw26282step2 raw26282step2Labels := by
      have ha : raw26282step2 = raw26282step1 := by apply Matrix.ext; unfold raw26282step2 raw26282step1; decide +kernel
      have hl : raw26282step1Labels = labelEmbedding7 ∘ raw26282step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26282step1 raw26282step1Labels raw26282step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4217 node4217Labels := by rfl

def raw26283 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw26283step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26283step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26283step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26283step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26283 raw26283Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw26283 raw26283Labels = mixedMoment B raw26283step0 raw26283step0Labels := by
      have hz : ∀ j, raw26283 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26283step0 = (fun i j => raw26283 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26283step0 raw26283; decide +kernel
      have hl : raw26283step0Labels = raw26283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26283 raw26283Labels permutation346 hz
    mixedMoment B raw26283step0 raw26283step0Labels = mixedMoment B raw26283step1 raw26283step1Labels := by
      have ha : raw26283step1 = (fun i j => raw26283step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26283step1 raw26283step0; decide +kernel
      have hl : raw26283step1Labels = raw26283step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26283step0 raw26283step0Labels permutation41 permutation4
    mixedMoment B raw26283step1 raw26283step1Labels = mixedMoment B raw26283step2 raw26283step2Labels := by
      have ha : raw26283step2 = -raw26283step1 := by apply Matrix.ext; change ∀ i j, raw26283step2 i j = -(raw26283step1 i j); unfold raw26283step2 raw26283step1; decide +kernel
      have hl : raw26283step2Labels = raw26283step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26283step2 raw26283step2Labels = mixedMoment B raw26283step3 raw26283step3Labels := by
      have ha : raw26283step3 = raw26283step2 := by apply Matrix.ext; unfold raw26283step3 raw26283step2; decide +kernel
      have hl : raw26283step2Labels = labelEmbedding7 ∘ raw26283step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26283step2 raw26283step2Labels raw26283step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4268 node4268Labels := by rfl

def raw26284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw26284step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26284step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26284step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw26284step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26284 raw26284Labels = mixedMoment B node4113 node4113Labels := by
  calc
    mixedMoment B raw26284 raw26284Labels = mixedMoment B raw26284step0 raw26284step0Labels := by
      have ha : raw26284step0 = (fun i j => raw26284 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26284step0 raw26284; decide +kernel
      have hl : raw26284step0Labels = raw26284Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26284 raw26284Labels permutation152 permutation4
    mixedMoment B raw26284step0 raw26284step0Labels = mixedMoment B raw26284step1 raw26284step1Labels := by
      have ha : raw26284step1 = -raw26284step0 := by apply Matrix.ext; change ∀ i j, raw26284step1 i j = -(raw26284step0 i j); unfold raw26284step1 raw26284step0; decide +kernel
      have hl : raw26284step1Labels = raw26284step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26284step1 raw26284step1Labels = mixedMoment B raw26284step2 raw26284step2Labels := by
      have ha : raw26284step2 = raw26284step1 := by apply Matrix.ext; unfold raw26284step2 raw26284step1; decide +kernel
      have hl : raw26284step1Labels = labelEmbedding7 ∘ raw26284step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26284step1 raw26284step1Labels raw26284step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4113 node4113Labels := by rfl

def raw26285 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26285step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26285step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26285step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26285 raw26285Labels = mixedMoment B node4267 node4267Labels := by
  calc
    mixedMoment B raw26285 raw26285Labels = mixedMoment B raw26285step0 raw26285step0Labels := by
      have hz : ∀ j, raw26285 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26285step0 = (fun i j => raw26285 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26285step0 raw26285; decide +kernel
      have hl : raw26285step0Labels = raw26285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26285 raw26285Labels permutation265 hz
    mixedMoment B raw26285step0 raw26285step0Labels = mixedMoment B raw26285step1 raw26285step1Labels := by
      have ha : raw26285step1 = (fun i j => raw26285step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26285step1 raw26285step0; decide +kernel
      have hl : raw26285step1Labels = raw26285step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26285step0 raw26285step0Labels permutation32 permutation6
    mixedMoment B raw26285step1 raw26285step1Labels = mixedMoment B raw26285step2 raw26285step2Labels := by
      have ha : raw26285step2 = raw26285step1 := by apply Matrix.ext; unfold raw26285step2 raw26285step1; decide +kernel
      have hl : raw26285step1Labels = labelEmbedding9 ∘ raw26285step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26285step1 raw26285step1Labels raw26285step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4267 node4267Labels := by rfl

def raw26286 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26286step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw26286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26286 raw26286Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw26286 raw26286Labels = mixedMoment B raw26286step0 raw26286step0Labels := by
      have ha : raw26286step0 = (fun i j => raw26286 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw26286step0 raw26286; decide +kernel
      have hl : raw26286step0Labels = raw26286Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26286 raw26286Labels permutation152 permutation6
    mixedMoment B raw26286step0 raw26286step0Labels = mixedMoment B raw26286step1 raw26286step1Labels := by
      have ha : raw26286step1 = raw26286step0 := by apply Matrix.ext; unfold raw26286step1 raw26286step0; decide +kernel
      have hl : raw26286step0Labels = labelEmbedding9 ∘ raw26286step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26286step0 raw26286step0Labels raw26286step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4249 node4249Labels := by rfl

def raw26287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26287step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26287step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26287step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26287step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26287 raw26287Labels = mixedMoment B node4119 node4119Labels := by
  calc
    mixedMoment B raw26287 raw26287Labels = mixedMoment B raw26287step0 raw26287step0Labels := by
      have hz : ∀ j, raw26287 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26287step0 = (fun i j => raw26287 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26287step0 raw26287; decide +kernel
      have hl : raw26287step0Labels = raw26287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26287 raw26287Labels permutation346 hz
    mixedMoment B raw26287step0 raw26287step0Labels = mixedMoment B raw26287step1 raw26287step1Labels := by
      have ha : raw26287step1 = (fun i j => raw26287step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26287step1 raw26287step0; decide +kernel
      have hl : raw26287step1Labels = raw26287step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26287step0 raw26287step0Labels permutation35 permutation4
    mixedMoment B raw26287step1 raw26287step1Labels = mixedMoment B raw26287step2 raw26287step2Labels := by
      have ha : raw26287step2 = -raw26287step1 := by apply Matrix.ext; change ∀ i j, raw26287step2 i j = -(raw26287step1 i j); unfold raw26287step2 raw26287step1; decide +kernel
      have hl : raw26287step2Labels = raw26287step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26287step2 raw26287step2Labels = mixedMoment B raw26287step3 raw26287step3Labels := by
      have ha : raw26287step3 = raw26287step2 := by apply Matrix.ext; unfold raw26287step3 raw26287step2; decide +kernel
      have hl : raw26287step2Labels = labelEmbedding7 ∘ raw26287step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26287step2 raw26287step2Labels raw26287step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4119 node4119Labels := by rfl

def raw26288 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw26288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26288step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26288step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26288step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26288step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26288step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26288 raw26288Labels = mixedMoment B node4210 node4210Labels := by
  calc
    mixedMoment B raw26288 raw26288Labels = mixedMoment B raw26288step0 raw26288step0Labels := by
      have ha : raw26288step0 = (fun i j => raw26288 (permutation179 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26288step0 raw26288; decide +kernel
      have hl : raw26288step0Labels = raw26288Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26288 raw26288Labels permutation179 permutation4
    mixedMoment B raw26288step0 raw26288step0Labels = mixedMoment B raw26288step1 raw26288step1Labels := by
      have ha : raw26288step1 = -raw26288step0 := by apply Matrix.ext; change ∀ i j, raw26288step1 i j = -(raw26288step0 i j); unfold raw26288step1 raw26288step0; decide +kernel
      have hl : raw26288step1Labels = raw26288step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26288step1 raw26288step1Labels = mixedMoment B raw26288step2 raw26288step2Labels := by
      have ha : raw26288step2 = raw26288step1 := by apply Matrix.ext; unfold raw26288step2 raw26288step1; decide +kernel
      have hl : raw26288step1Labels = labelEmbedding7 ∘ raw26288step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26288step1 raw26288step1Labels raw26288step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4210 node4210Labels := by rfl

def raw26289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw26289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw26289step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26289step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26289step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26289step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26289step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26289step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26289 raw26289Labels = mixedMoment B node4119 node4119Labels := by
  calc
    mixedMoment B raw26289 raw26289Labels = mixedMoment B raw26289step0 raw26289step0Labels := by
      have hz : ∀ j, raw26289 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26289step0 = (fun i j => raw26289 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26289step0 raw26289; decide +kernel
      have hl : raw26289step0Labels = raw26289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26289 raw26289Labels permutation346 hz
    mixedMoment B raw26289step0 raw26289step0Labels = mixedMoment B raw26289step1 raw26289step1Labels := by
      have ha : raw26289step1 = (fun i j => raw26289step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26289step1 raw26289step0; decide +kernel
      have hl : raw26289step1Labels = raw26289step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26289step0 raw26289step0Labels permutation33 permutation4
    mixedMoment B raw26289step1 raw26289step1Labels = mixedMoment B raw26289step2 raw26289step2Labels := by
      have ha : raw26289step2 = -raw26289step1 := by apply Matrix.ext; change ∀ i j, raw26289step2 i j = -(raw26289step1 i j); unfold raw26289step2 raw26289step1; decide +kernel
      have hl : raw26289step2Labels = raw26289step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26289step2 raw26289step2Labels = mixedMoment B raw26289step3 raw26289step3Labels := by
      have ha : raw26289step3 = raw26289step2 := by apply Matrix.ext; unfold raw26289step3 raw26289step2; decide +kernel
      have hl : raw26289step2Labels = labelEmbedding7 ∘ raw26289step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26289step2 raw26289step2Labels raw26289step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4119 node4119Labels := by rfl

def raw26290 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw26290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw26290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26290step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw26290step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26290step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26290step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26290step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26290step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26290step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26290step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26290 raw26290Labels = mixedMoment B node4283 node4283Labels := by
  calc
    mixedMoment B raw26290 raw26290Labels = mixedMoment B raw26290step0 raw26290step0Labels := by
      have hz : ∀ j, raw26290 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26290step0 = (fun i j => raw26290 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26290step0 raw26290; decide +kernel
      have hl : raw26290step0Labels = raw26290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26290 raw26290Labels permutation346 hz
    mixedMoment B raw26290step0 raw26290step0Labels = mixedMoment B raw26290step1 raw26290step1Labels := by
      have hz : ∀ j, raw26290step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26290step1 = (fun i j => raw26290step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26290step1 raw26290step0; decide +kernel
      have hl : raw26290step1Labels = raw26290step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26290step0 raw26290step0Labels permutation56 hz
    mixedMoment B raw26290step1 raw26290step1Labels = mixedMoment B raw26290step2 raw26290step2Labels := by
      have ha : raw26290step2 = (fun i j => raw26290step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26290step2 raw26290step1; decide +kernel
      have hl : raw26290step2Labels = raw26290step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26290step1 raw26290step1Labels permutation9 permutation4
    mixedMoment B raw26290step2 raw26290step2Labels = mixedMoment B raw26290step3 raw26290step3Labels := by
      have ha : raw26290step3 = -raw26290step2 := by apply Matrix.ext; change ∀ i j, raw26290step3 i j = -(raw26290step2 i j); unfold raw26290step3 raw26290step2; decide +kernel
      have hl : raw26290step3Labels = raw26290step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26290step3 raw26290step3Labels = mixedMoment B raw26290step4 raw26290step4Labels := by
      have ha : raw26290step4 = raw26290step3 := by apply Matrix.ext; unfold raw26290step4 raw26290step3; decide +kernel
      have hl : raw26290step3Labels = labelEmbedding7 ∘ raw26290step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26290step3 raw26290step3Labels raw26290step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4283 node4283Labels := by rfl

def raw26291 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw26291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26291step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26291step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26291step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26291step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26291step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26291 raw26291Labels = mixedMoment B node4210 node4210Labels := by
  calc
    mixedMoment B raw26291 raw26291Labels = mixedMoment B raw26291step0 raw26291step0Labels := by
      have ha : raw26291step0 = (fun i j => raw26291 (permutation177 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26291step0 raw26291; decide +kernel
      have hl : raw26291step0Labels = raw26291Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26291 raw26291Labels permutation177 permutation4
    mixedMoment B raw26291step0 raw26291step0Labels = mixedMoment B raw26291step1 raw26291step1Labels := by
      have ha : raw26291step1 = -raw26291step0 := by apply Matrix.ext; change ∀ i j, raw26291step1 i j = -(raw26291step0 i j); unfold raw26291step1 raw26291step0; decide +kernel
      have hl : raw26291step1Labels = raw26291step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26291step1 raw26291step1Labels = mixedMoment B raw26291step2 raw26291step2Labels := by
      have ha : raw26291step2 = raw26291step1 := by apply Matrix.ext; unfold raw26291step2 raw26291step1; decide +kernel
      have hl : raw26291step1Labels = labelEmbedding7 ∘ raw26291step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26291step1 raw26291step1Labels raw26291step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4210 node4210Labels := by rfl

def raw26292 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw26292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw26292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw26292step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26292step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26292step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26292step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26292 raw26292Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw26292 raw26292Labels = mixedMoment B raw26292step0 raw26292step0Labels := by
      have hz : ∀ j, raw26292 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26292step0 = (fun i j => raw26292 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26292step0 raw26292; decide +kernel
      have hl : raw26292step0Labels = raw26292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26292 raw26292Labels permutation346 hz
    mixedMoment B raw26292step0 raw26292step0Labels = mixedMoment B raw26292step1 raw26292step1Labels := by
      have ha : raw26292step1 = (fun i j => raw26292step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26292step1 raw26292step0; decide +kernel
      have hl : raw26292step1Labels = raw26292step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26292step0 raw26292step0Labels permutation39 permutation4
    mixedMoment B raw26292step1 raw26292step1Labels = mixedMoment B raw26292step2 raw26292step2Labels := by
      have ha : raw26292step2 = -raw26292step1 := by apply Matrix.ext; change ∀ i j, raw26292step2 i j = -(raw26292step1 i j); unfold raw26292step2 raw26292step1; decide +kernel
      have hl : raw26292step2Labels = raw26292step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26292step2 raw26292step2Labels = mixedMoment B raw26292step3 raw26292step3Labels := by
      have ha : raw26292step3 = raw26292step2 := by apply Matrix.ext; unfold raw26292step3 raw26292step2; decide +kernel
      have hl : raw26292step2Labels = labelEmbedding7 ∘ raw26292step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26292step2 raw26292step2Labels raw26292step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4265 node4265Labels := by rfl

def raw26293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 5, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw26293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![5, -1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw26293step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26293step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw26293step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26293step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26293 raw26293Labels = mixedMoment B node4118 node4118Labels := by
  calc
    mixedMoment B raw26293 raw26293Labels = mixedMoment B raw26293step0 raw26293step0Labels := by
      have hz : ∀ j, raw26293 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26293step0 = (fun i j => raw26293 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26293step0 raw26293; decide +kernel
      have hl : raw26293step0Labels = raw26293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26293 raw26293Labels permutation346 hz
    mixedMoment B raw26293step0 raw26293step0Labels = mixedMoment B raw26293step1 raw26293step1Labels := by
      have ha : raw26293step1 = (fun i j => raw26293step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26293step1 raw26293step0; decide +kernel
      have hl : raw26293step1Labels = raw26293step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26293step0 raw26293step0Labels permutation32 permutation4
    mixedMoment B raw26293step1 raw26293step1Labels = mixedMoment B raw26293step2 raw26293step2Labels := by
      have ha : raw26293step2 = -raw26293step1 := by apply Matrix.ext; change ∀ i j, raw26293step2 i j = -(raw26293step1 i j); unfold raw26293step2 raw26293step1; decide +kernel
      have hl : raw26293step2Labels = raw26293step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26293step2 raw26293step2Labels = mixedMoment B raw26293step3 raw26293step3Labels := by
      have ha : raw26293step3 = raw26293step2 := by apply Matrix.ext; unfold raw26293step3 raw26293step2; decide +kernel
      have hl : raw26293step2Labels = labelEmbedding7 ∘ raw26293step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26293step2 raw26293step2Labels raw26293step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4118 node4118Labels := by rfl

def raw26294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw26294step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw26294step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26294step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw26294step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26294 raw26294Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw26294 raw26294Labels = mixedMoment B raw26294step0 raw26294step0Labels := by
      have hz : ∀ j, raw26294 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26294step0 = (fun i j => raw26294 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26294step0 raw26294; decide +kernel
      have hl : raw26294step0Labels = raw26294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26294 raw26294Labels permutation346 hz
    mixedMoment B raw26294step0 raw26294step0Labels = mixedMoment B raw26294step1 raw26294step1Labels := by
      have ha : raw26294step1 = (fun i j => raw26294step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26294step1 raw26294step0; decide +kernel
      have hl : raw26294step1Labels = raw26294step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26294step0 raw26294step0Labels permutation44 permutation7
    mixedMoment B raw26294step1 raw26294step1Labels = mixedMoment B raw26294step2 raw26294step2Labels := by
      have ha : raw26294step2 = -raw26294step1 := by apply Matrix.ext; change ∀ i j, raw26294step2 i j = -(raw26294step1 i j); unfold raw26294step2 raw26294step1; decide +kernel
      have hl : raw26294step2Labels = raw26294step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26294step2 raw26294step2Labels = mixedMoment B raw26294step3 raw26294step3Labels := by
      have ha : raw26294step3 = raw26294step2 := by apply Matrix.ext; unfold raw26294step3 raw26294step2; decide +kernel
      have hl : raw26294step2Labels = labelEmbedding10 ∘ raw26294step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26294step2 raw26294step2Labels raw26294step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

def raw26295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw26295step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26295step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26295step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26295step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26295step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26295 raw26295Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw26295 raw26295Labels = mixedMoment B raw26295step0 raw26295step0Labels := by
      have ha : raw26295step0 = (fun i j => raw26295 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26295step0 raw26295; decide +kernel
      have hl : raw26295step0Labels = raw26295Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26295 raw26295Labels permutation188 permutation7
    mixedMoment B raw26295step0 raw26295step0Labels = mixedMoment B raw26295step1 raw26295step1Labels := by
      have ha : raw26295step1 = -raw26295step0 := by apply Matrix.ext; change ∀ i j, raw26295step1 i j = -(raw26295step0 i j); unfold raw26295step1 raw26295step0; decide +kernel
      have hl : raw26295step1Labels = raw26295step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26295step1 raw26295step1Labels = mixedMoment B raw26295step2 raw26295step2Labels := by
      have ha : raw26295step2 = raw26295step1 := by apply Matrix.ext; unfold raw26295step2 raw26295step1; decide +kernel
      have hl : raw26295step1Labels = labelEmbedding10 ∘ raw26295step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26295step1 raw26295step1Labels raw26295step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

def raw26296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw26296step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26296step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26296step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26296step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26296step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26296 raw26296Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw26296 raw26296Labels = mixedMoment B raw26296step0 raw26296step0Labels := by
      have hz : ∀ j, raw26296 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26296step0 = (fun i j => raw26296 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26296step0 raw26296; decide +kernel
      have hl : raw26296step0Labels = raw26296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26296 raw26296Labels permutation346 hz
    mixedMoment B raw26296step0 raw26296step0Labels = mixedMoment B raw26296step1 raw26296step1Labels := by
      have ha : raw26296step1 = (fun i j => raw26296step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26296step1 raw26296step0; decide +kernel
      have hl : raw26296step1Labels = raw26296step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26296step0 raw26296step0Labels permutation44 permutation7
    mixedMoment B raw26296step1 raw26296step1Labels = mixedMoment B raw26296step2 raw26296step2Labels := by
      have ha : raw26296step2 = -raw26296step1 := by apply Matrix.ext; change ∀ i j, raw26296step2 i j = -(raw26296step1 i j); unfold raw26296step2 raw26296step1; decide +kernel
      have hl : raw26296step2Labels = raw26296step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26296step2 raw26296step2Labels = mixedMoment B raw26296step3 raw26296step3Labels := by
      have ha : raw26296step3 = raw26296step2 := by apply Matrix.ext; unfold raw26296step3 raw26296step2; decide +kernel
      have hl : raw26296step2Labels = labelEmbedding10 ∘ raw26296step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26296step2 raw26296step2Labels raw26296step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4457 node4457Labels := by rfl

def raw26297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw26297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw26297step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26297step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26297step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26297step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26297step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26297 raw26297Labels = mixedMoment B node4498 node4498Labels := by
  calc
    mixedMoment B raw26297 raw26297Labels = mixedMoment B raw26297step0 raw26297step0Labels := by
      have hz : ∀ j, raw26297 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26297step0 = (fun i j => raw26297 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26297step0 raw26297; decide +kernel
      have hl : raw26297step0Labels = raw26297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26297 raw26297Labels permutation520 hz
    mixedMoment B raw26297step0 raw26297step0Labels = mixedMoment B raw26297step1 raw26297step1Labels := by
      have hz : ∀ j, raw26297step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw26297step1 = (fun i j => raw26297step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw26297step1 raw26297step0; decide +kernel
      have hl : raw26297step1Labels = raw26297step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26297step0 raw26297step0Labels permutation80 hz
    mixedMoment B raw26297step1 raw26297step1Labels = mixedMoment B raw26297step2 raw26297step2Labels := by
      have ha : raw26297step2 = (fun i j => raw26297step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26297step2 raw26297step1; decide +kernel
      have hl : raw26297step2Labels = raw26297step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26297step1 raw26297step1Labels permutation8 permutation7
    mixedMoment B raw26297step2 raw26297step2Labels = mixedMoment B raw26297step3 raw26297step3Labels := by
      have ha : raw26297step3 = -raw26297step2 := by apply Matrix.ext; change ∀ i j, raw26297step3 i j = -(raw26297step2 i j); unfold raw26297step3 raw26297step2; decide +kernel
      have hl : raw26297step3Labels = raw26297step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26297step3 raw26297step3Labels = mixedMoment B raw26297step4 raw26297step4Labels := by
      have ha : raw26297step4 = raw26297step3 := by apply Matrix.ext; unfold raw26297step4 raw26297step3; decide +kernel
      have hl : raw26297step3Labels = labelEmbedding10 ∘ raw26297step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26297step3 raw26297step3Labels raw26297step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4498 node4498Labels := by rfl

def raw26298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw26298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw26298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw26298step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26298step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26298step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26298step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26298step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26298 raw26298Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw26298 raw26298Labels = mixedMoment B raw26298step0 raw26298step0Labels := by
      have hz : ∀ j, raw26298 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26298step0 = (fun i j => raw26298 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26298step0 raw26298; decide +kernel
      have hl : raw26298step0Labels = raw26298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26298 raw26298Labels permutation346 hz
    mixedMoment B raw26298step0 raw26298step0Labels = mixedMoment B raw26298step1 raw26298step1Labels := by
      have ha : raw26298step1 = (fun i j => raw26298step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26298step1 raw26298step0; decide +kernel
      have hl : raw26298step1Labels = raw26298step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26298step0 raw26298step0Labels permutation44 permutation7
    mixedMoment B raw26298step1 raw26298step1Labels = mixedMoment B raw26298step2 raw26298step2Labels := by
      have ha : raw26298step2 = -raw26298step1 := by apply Matrix.ext; change ∀ i j, raw26298step2 i j = -(raw26298step1 i j); unfold raw26298step2 raw26298step1; decide +kernel
      have hl : raw26298step2Labels = raw26298step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26298step2 raw26298step2Labels = mixedMoment B raw26298step3 raw26298step3Labels := by
      have ha : raw26298step3 = raw26298step2 := by apply Matrix.ext; unfold raw26298step3 raw26298step2; decide +kernel
      have hl : raw26298step2Labels = labelEmbedding10 ∘ raw26298step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26298step2 raw26298step2Labels raw26298step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw26299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26299step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26299step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26299 raw26299Labels = mixedMoment B node4118 node4118Labels := by
  calc
    mixedMoment B raw26299 raw26299Labels = mixedMoment B raw26299step0 raw26299step0Labels := by
      have hz : ∀ j, raw26299 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26299step0 = (fun i j => raw26299 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26299step0 raw26299; decide +kernel
      have hl : raw26299step0Labels = raw26299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26299 raw26299Labels permutation346 hz
    mixedMoment B raw26299step0 raw26299step0Labels = mixedMoment B raw26299step1 raw26299step1Labels := by
      have ha : raw26299step1 = (fun i j => raw26299step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26299step1 raw26299step0; decide +kernel
      have hl : raw26299step1Labels = raw26299step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26299step0 raw26299step0Labels permutation44 permutation2
    _ = mixedMoment B node4118 node4118Labels := by rfl

def raw26300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26300step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26300 raw26300Labels = mixedMoment B node4209 node4209Labels := by
  calc
    mixedMoment B raw26300 raw26300Labels = mixedMoment B raw26300step0 raw26300step0Labels := by
      have ha : raw26300step0 = (fun i j => raw26300 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26300step0 raw26300; decide +kernel
      have hl : raw26300step0Labels = raw26300Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26300 raw26300Labels permutation188 permutation2
    _ = mixedMoment B node4209 node4209Labels := by rfl

def raw26301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26301step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26301step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26301 raw26301Labels = mixedMoment B node4264 node4264Labels := by
  calc
    mixedMoment B raw26301 raw26301Labels = mixedMoment B raw26301step0 raw26301step0Labels := by
      have hz : ∀ j, raw26301 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26301step0 = (fun i j => raw26301 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26301step0 raw26301; decide +kernel
      have hl : raw26301step0Labels = raw26301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26301 raw26301Labels permutation346 hz
    mixedMoment B raw26301step0 raw26301step0Labels = mixedMoment B raw26301step1 raw26301step1Labels := by
      have ha : raw26301step1 = (fun i j => raw26301step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26301step1 raw26301step0; decide +kernel
      have hl : raw26301step1Labels = raw26301step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26301step0 raw26301step0Labels permutation40 permutation2
    _ = mixedMoment B node4264 node4264Labels := by rfl

def raw26302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw26302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26302step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw26302step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26302step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw26302step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw26302step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw26302step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26302 raw26302Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw26302 raw26302Labels = mixedMoment B raw26302step0 raw26302step0Labels := by
      have hz : ∀ j, raw26302 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26302step0 = (fun i j => raw26302 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26302step0 raw26302; decide +kernel
      have hl : raw26302step0Labels = raw26302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26302 raw26302Labels permutation520 hz
    mixedMoment B raw26302step0 raw26302step0Labels = mixedMoment B raw26302step1 raw26302step1Labels := by
      have hz : ∀ j, raw26302step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw26302step1 = (fun i j => raw26302step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw26302step1 raw26302step0; decide +kernel
      have hl : raw26302step1Labels = raw26302step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26302step0 raw26302step0Labels permutation80 hz
    mixedMoment B raw26302step1 raw26302step1Labels = mixedMoment B raw26302step2 raw26302step2Labels := by
      have hz : ∀ i, raw26302step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw26302step2 = (fun i j => raw26302step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw26302step2 raw26302step1; decide +kernel
      have hl : raw26302step2Labels = (fun j => raw26302step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26302step1 raw26302step1Labels permutation4 hz
    mixedMoment B raw26302step2 raw26302step2Labels = mixedMoment B raw26302step3 raw26302step3Labels := by
      have ha : raw26302step3 = raw26302step2 := by apply Matrix.ext; unfold raw26302step3 raw26302step2; decide +kernel
      have hl : raw26302step2Labels = labelEmbedding2 ∘ raw26302step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26302step2 raw26302step2Labels raw26302step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw26303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw26303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw26303step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26303step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26303step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26303step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26303step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26303step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26303 raw26303Labels = mixedMoment B node4267 node4267Labels := by
  calc
    mixedMoment B raw26303 raw26303Labels = mixedMoment B raw26303step0 raw26303step0Labels := by
      have hz : ∀ j, raw26303 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26303step0 = (fun i j => raw26303 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26303step0 raw26303; decide +kernel
      have hl : raw26303step0Labels = raw26303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26303 raw26303Labels permutation346 hz
    mixedMoment B raw26303step0 raw26303step0Labels = mixedMoment B raw26303step1 raw26303step1Labels := by
      have ha : raw26303step1 = (fun i j => raw26303step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26303step1 raw26303step0; decide +kernel
      have hl : raw26303step1Labels = raw26303step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26303step0 raw26303step0Labels permutation44 permutation7
    mixedMoment B raw26303step1 raw26303step1Labels = mixedMoment B raw26303step2 raw26303step2Labels := by
      have ha : raw26303step2 = -raw26303step1 := by apply Matrix.ext; change ∀ i j, raw26303step2 i j = -(raw26303step1 i j); unfold raw26303step2 raw26303step1; decide +kernel
      have hl : raw26303step2Labels = raw26303step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26303step2 raw26303step2Labels = mixedMoment B raw26303step3 raw26303step3Labels := by
      have ha : raw26303step3 = raw26303step2 := by apply Matrix.ext; unfold raw26303step3 raw26303step2; decide +kernel
      have hl : raw26303step2Labels = labelEmbedding10 ∘ raw26303step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26303step2 raw26303step2Labels raw26303step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4267 node4267Labels := by rfl

def raw26304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26304step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26304step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26304 raw26304Labels = mixedMoment B node4098 node4098Labels := by
  calc
    mixedMoment B raw26304 raw26304Labels = mixedMoment B raw26304step0 raw26304step0Labels := by
      have ha : raw26304step0 = (fun i j => raw26304 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26304step0 raw26304; decide +kernel
      have hl : raw26304step0Labels = raw26304Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26304 raw26304Labels permutation154 permutation2
    _ = mixedMoment B node4098 node4098Labels := by rfl

def raw26305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26305step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26305 raw26305Labels = mixedMoment B node4230 node4230Labels := by
  calc
    mixedMoment B raw26305 raw26305Labels = mixedMoment B raw26305step0 raw26305step0Labels := by
      have ha : raw26305step0 = (fun i j => raw26305 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26305step0 raw26305; decide +kernel
      have hl : raw26305step0Labels = raw26305Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26305 raw26305Labels permutation154 permutation2
    _ = mixedMoment B node4230 node4230Labels := by rfl

def raw26306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26306step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw26306step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26306 raw26306Labels = mixedMoment B node4248 node4248Labels := by
  calc
    mixedMoment B raw26306 raw26306Labels = mixedMoment B raw26306step0 raw26306step0Labels := by
      have ha : raw26306step0 = (fun i j => raw26306 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26306step0 raw26306; decide +kernel
      have hl : raw26306step0Labels = raw26306Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26306 raw26306Labels permutation158 permutation2
    _ = mixedMoment B node4248 node4248Labels := by rfl

def raw26307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2]]
def raw26307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw26307step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26307 raw26307Labels = mixedMoment B node4264 node4264Labels := by
  calc
    mixedMoment B raw26307 raw26307Labels = mixedMoment B raw26307step0 raw26307step0Labels := by
      have hz : ∀ j, raw26307 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26307step0 = (fun i j => raw26307 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26307step0 raw26307; decide +kernel
      have hl : raw26307step0Labels = raw26307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26307 raw26307Labels permutation520 hz
    _ = mixedMoment B node4264 node4264Labels := by rfl

def raw26308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 1, -2]]
def raw26308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw26308step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26308step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26308step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26308step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw26308step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26308 raw26308Labels = mixedMoment B node4249 node4249Labels := by
  calc
    mixedMoment B raw26308 raw26308Labels = mixedMoment B raw26308step0 raw26308step0Labels := by
      have ha : raw26308step0 = (fun i j => raw26308 (permutation188 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26308step0 raw26308; decide +kernel
      have hl : raw26308step0Labels = raw26308Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26308 raw26308Labels permutation188 permutation7
    mixedMoment B raw26308step0 raw26308step0Labels = mixedMoment B raw26308step1 raw26308step1Labels := by
      have ha : raw26308step1 = -raw26308step0 := by apply Matrix.ext; change ∀ i j, raw26308step1 i j = -(raw26308step0 i j); unfold raw26308step1 raw26308step0; decide +kernel
      have hl : raw26308step1Labels = raw26308step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26308step1 raw26308step1Labels = mixedMoment B raw26308step2 raw26308step2Labels := by
      have ha : raw26308step2 = raw26308step1 := by apply Matrix.ext; unfold raw26308step2 raw26308step1; decide +kernel
      have hl : raw26308step1Labels = labelEmbedding10 ∘ raw26308step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26308step1 raw26308step1Labels raw26308step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4249 node4249Labels := by rfl

def raw26309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26309step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw26309step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26309 raw26309Labels = mixedMoment B node4102 node4102Labels := by
  calc
    mixedMoment B raw26309 raw26309Labels = mixedMoment B raw26309step0 raw26309step0Labels := by
      have hz : ∀ j, raw26309 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26309step0 = (fun i j => raw26309 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26309step0 raw26309; decide +kernel
      have hl : raw26309step0Labels = raw26309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26309 raw26309Labels permutation346 hz
    mixedMoment B raw26309step0 raw26309step0Labels = mixedMoment B raw26309step1 raw26309step1Labels := by
      have ha : raw26309step1 = (fun i j => raw26309step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26309step1 raw26309step0; decide +kernel
      have hl : raw26309step1Labels = raw26309step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26309step0 raw26309step0Labels permutation34 permutation2
    _ = mixedMoment B node4102 node4102Labels := by rfl

def raw26310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26310step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw26310step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26310 raw26310Labels = mixedMoment B node4234 node4234Labels := by
  calc
    mixedMoment B raw26310 raw26310Labels = mixedMoment B raw26310step0 raw26310step0Labels := by
      have hz : ∀ j, raw26310 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26310step0 = (fun i j => raw26310 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26310step0 raw26310; decide +kernel
      have hl : raw26310step0Labels = raw26310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26310 raw26310Labels permutation346 hz
    mixedMoment B raw26310step0 raw26310step0Labels = mixedMoment B raw26310step1 raw26310step1Labels := by
      have ha : raw26310step1 = (fun i j => raw26310step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26310step1 raw26310step0; decide +kernel
      have hl : raw26310step1Labels = raw26310step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26310step0 raw26310step0Labels permutation34 permutation2
    _ = mixedMoment B node4234 node4234Labels := by rfl

def raw26311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw26311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26311step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw26311step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26311 raw26311Labels = mixedMoment B node4197 node4197Labels := by
  calc
    mixedMoment B raw26311 raw26311Labels = mixedMoment B raw26311step0 raw26311step0Labels := by
      have ha : raw26311step0 = (fun i j => raw26311 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26311step0 raw26311; decide +kernel
      have hl : raw26311step0Labels = raw26311Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26311 raw26311Labels permutation178 permutation2
    _ = mixedMoment B node4197 node4197Labels := by rfl

def raw26312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0], ![2, 0, -2]]
def raw26312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, 0, -2]]
def raw26312step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26312step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26312step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26312 raw26312Labels = mixedMoment B node4273 node4273Labels := by
  calc
    mixedMoment B raw26312 raw26312Labels = mixedMoment B raw26312step0 raw26312step0Labels := by
      have hz : ∀ j, raw26312 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26312step0 = (fun i j => raw26312 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26312step0 raw26312; decide +kernel
      have hl : raw26312step0Labels = raw26312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26312 raw26312Labels permutation520 hz
    mixedMoment B raw26312step0 raw26312step0Labels = mixedMoment B raw26312step1 raw26312step1Labels := by
      have hz : ∀ j, raw26312step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw26312step1 = (fun i j => raw26312step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw26312step1 raw26312step0; decide +kernel
      have hl : raw26312step1Labels = raw26312step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26312step0 raw26312step0Labels permutation80 hz
    _ = mixedMoment B node4273 node4273Labels := by rfl

def raw26313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw26313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw26313step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26313step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26313 raw26313Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw26313 raw26313Labels = mixedMoment B raw26313step0 raw26313step0Labels := by
      have hz : ∀ j, raw26313 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26313step0 = (fun i j => raw26313 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26313step0 raw26313; decide +kernel
      have hl : raw26313step0Labels = raw26313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26313 raw26313Labels permutation346 hz
    mixedMoment B raw26313step0 raw26313step0Labels = mixedMoment B raw26313step1 raw26313step1Labels := by
      have ha : raw26313step1 = (fun i j => raw26313step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26313step1 raw26313step0; decide +kernel
      have hl : raw26313step1Labels = raw26313step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26313step0 raw26313step0Labels permutation35 permutation2
    _ = mixedMoment B node4265 node4265Labels := by rfl

def raw26314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw26314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw26314step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26314 raw26314Labels = mixedMoment B node4106 node4106Labels := by
  calc
    mixedMoment B raw26314 raw26314Labels = mixedMoment B raw26314step0 raw26314step0Labels := by
      have hz : ∀ j, raw26314 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26314step0 = (fun i j => raw26314 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26314step0 raw26314; decide +kernel
      have hl : raw26314step0Labels = raw26314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26314 raw26314Labels permutation346 hz
    _ = mixedMoment B node4106 node4106Labels := by rfl

def raw26315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw26315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw26315step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26315 raw26315Labels = mixedMoment B node4238 node4238Labels := by
  calc
    mixedMoment B raw26315 raw26315Labels = mixedMoment B raw26315step0 raw26315step0Labels := by
      have hz : ∀ j, raw26315 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26315step0 = (fun i j => raw26315 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26315step0 raw26315; decide +kernel
      have hl : raw26315step0Labels = raw26315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26315 raw26315Labels permutation346 hz
    _ = mixedMoment B node4238 node4238Labels := by rfl

def raw26316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw26316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw26316step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26316 raw26316Labels = mixedMoment B node4200 node4200Labels := by
  calc
    mixedMoment B raw26316 raw26316Labels = mixedMoment B raw26316step0 raw26316step0Labels := by
      have ha : raw26316step0 = (fun i j => raw26316 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26316step0 raw26316; decide +kernel
      have hl : raw26316step0Labels = raw26316Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26316 raw26316Labels permutation176 permutation2
    _ = mixedMoment B node4200 node4200Labels := by rfl

def raw26317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw26317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw26317step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26317 raw26317Labels = mixedMoment B node4255 node4255Labels := by
  calc
    mixedMoment B raw26317 raw26317Labels = mixedMoment B raw26317step0 raw26317step0Labels := by
      have hz : ∀ j, raw26317 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26317step0 = (fun i j => raw26317 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26317step0 raw26317; decide +kernel
      have hl : raw26317step0Labels = raw26317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26317 raw26317Labels permutation346 hz
    _ = mixedMoment B node4255 node4255Labels := by rfl

def raw26318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw26318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 1, -2]]
def raw26318step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26318step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26318 raw26318Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw26318 raw26318Labels = mixedMoment B raw26318step0 raw26318step0Labels := by
      have hz : ∀ j, raw26318 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26318step0 = (fun i j => raw26318 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26318step0 raw26318; decide +kernel
      have hl : raw26318step0Labels = raw26318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26318 raw26318Labels permutation346 hz
    mixedMoment B raw26318step0 raw26318step0Labels = mixedMoment B raw26318step1 raw26318step1Labels := by
      have ha : raw26318step1 = (fun i j => raw26318step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26318step1 raw26318step0; decide +kernel
      have hl : raw26318step1Labels = raw26318step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26318step0 raw26318step0Labels permutation33 permutation2
    _ = mixedMoment B node4268 node4268Labels := by rfl

def raw26319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw26319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw26319step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw26319step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26319 raw26319Labels = mixedMoment B node4101 node4101Labels := by
  calc
    mixedMoment B raw26319 raw26319Labels = mixedMoment B raw26319step0 raw26319step0Labels := by
      have hz : ∀ j, raw26319 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26319step0 = (fun i j => raw26319 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26319step0 raw26319; decide +kernel
      have hl : raw26319step0Labels = raw26319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26319 raw26319Labels permutation346 hz
    mixedMoment B raw26319step0 raw26319step0Labels = mixedMoment B raw26319step1 raw26319step1Labels := by
      have ha : raw26319step1 = (fun i j => raw26319step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26319step1 raw26319step0; decide +kernel
      have hl : raw26319step1Labels = raw26319step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26319step0 raw26319step0Labels permutation34 permutation2
    _ = mixedMoment B node4101 node4101Labels := by rfl

def raw26320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw26320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw26320step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw26320step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26320 raw26320Labels = mixedMoment B node4233 node4233Labels := by
  calc
    mixedMoment B raw26320 raw26320Labels = mixedMoment B raw26320step0 raw26320step0Labels := by
      have hz : ∀ j, raw26320 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26320step0 = (fun i j => raw26320 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26320step0 raw26320; decide +kernel
      have hl : raw26320step0Labels = raw26320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26320 raw26320Labels permutation346 hz
    mixedMoment B raw26320step0 raw26320step0Labels = mixedMoment B raw26320step1 raw26320step1Labels := by
      have ha : raw26320step1 = (fun i j => raw26320step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26320step1 raw26320step0; decide +kernel
      have hl : raw26320step1Labels = raw26320step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26320step0 raw26320step0Labels permutation34 permutation2
    _ = mixedMoment B node4233 node4233Labels := by rfl

def raw26321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw26321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw26321step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26321 raw26321Labels = mixedMoment B node4196 node4196Labels := by
  calc
    mixedMoment B raw26321 raw26321Labels = mixedMoment B raw26321step0 raw26321step0Labels := by
      have ha : raw26321step0 = (fun i j => raw26321 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26321step0 raw26321; decide +kernel
      have hl : raw26321step0Labels = raw26321Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26321 raw26321Labels permutation178 permutation2
    _ = mixedMoment B node4196 node4196Labels := by rfl

def raw26322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw26322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw26322step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26322 raw26322Labels = mixedMoment B node4251 node4251Labels := by
  calc
    mixedMoment B raw26322 raw26322Labels = mixedMoment B raw26322step0 raw26322step0Labels := by
      have hz : ∀ j, raw26322 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26322step0 = (fun i j => raw26322 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26322step0 raw26322; decide +kernel
      have hl : raw26322step0Labels = raw26322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26322 raw26322Labels permutation346 hz
    _ = mixedMoment B node4251 node4251Labels := by rfl

def raw26323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw26323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw26323step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26323step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw26323step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26323 raw26323Labels = mixedMoment B node4269 node4269Labels := by
  calc
    mixedMoment B raw26323 raw26323Labels = mixedMoment B raw26323step0 raw26323step0Labels := by
      have hz : ∀ j, raw26323 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26323step0 = (fun i j => raw26323 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26323step0 raw26323; decide +kernel
      have hl : raw26323step0Labels = raw26323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26323 raw26323Labels permutation520 hz
    mixedMoment B raw26323step0 raw26323step0Labels = mixedMoment B raw26323step1 raw26323step1Labels := by
      have hz : ∀ j, raw26323step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw26323step1 = (fun i j => raw26323step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw26323step1 raw26323step0; decide +kernel
      have hl : raw26323step1Labels = raw26323step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26323step0 raw26323step0Labels permutation80 hz
    _ = mixedMoment B node4269 node4269Labels := by rfl

def raw26324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26324step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26324step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26324step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26324step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26324step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26324 raw26324Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw26324 raw26324Labels = mixedMoment B raw26324step0 raw26324step0Labels := by
      have hz : ∀ j, raw26324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26324step0 = (fun i j => raw26324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26324step0 raw26324; decide +kernel
      have hl : raw26324step0Labels = raw26324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26324 raw26324Labels permutation346 hz
    mixedMoment B raw26324step0 raw26324step0Labels = mixedMoment B raw26324step1 raw26324step1Labels := by
      have ha : raw26324step1 = (fun i j => raw26324step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26324step1 raw26324step0; decide +kernel
      have hl : raw26324step1Labels = raw26324step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26324step0 raw26324step0Labels permutation35 permutation7
    mixedMoment B raw26324step1 raw26324step1Labels = mixedMoment B raw26324step2 raw26324step2Labels := by
      have ha : raw26324step2 = -raw26324step1 := by apply Matrix.ext; change ∀ i j, raw26324step2 i j = -(raw26324step1 i j); unfold raw26324step2 raw26324step1; decide +kernel
      have hl : raw26324step2Labels = raw26324step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26324step2 raw26324step2Labels = mixedMoment B raw26324step3 raw26324step3Labels := by
      have ha : raw26324step3 = raw26324step2 := by apply Matrix.ext; unfold raw26324step3 raw26324step2; decide +kernel
      have hl : raw26324step2Labels = labelEmbedding10 ∘ raw26324step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26324step2 raw26324step2Labels raw26324step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4424 node4424Labels := by rfl

def raw26325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26325step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw26325step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26325step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26325step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26325step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26325step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26325 raw26325Labels = mixedMoment B node4424 node4424Labels := by
  calc
    mixedMoment B raw26325 raw26325Labels = mixedMoment B raw26325step0 raw26325step0Labels := by
      have hz : ∀ j, raw26325 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26325step0 = (fun i j => raw26325 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26325step0 raw26325; decide +kernel
      have hl : raw26325step0Labels = raw26325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26325 raw26325Labels permutation265 hz
    mixedMoment B raw26325step0 raw26325step0Labels = mixedMoment B raw26325step1 raw26325step1Labels := by
      have ha : raw26325step1 = (fun i j => raw26325step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26325step1 raw26325step0; decide +kernel
      have hl : raw26325step1Labels = raw26325step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26325step0 raw26325step0Labels permutation35 permutation7
    mixedMoment B raw26325step1 raw26325step1Labels = mixedMoment B raw26325step2 raw26325step2Labels := by
      have ha : raw26325step2 = -raw26325step1 := by apply Matrix.ext; change ∀ i j, raw26325step2 i j = -(raw26325step1 i j); unfold raw26325step2 raw26325step1; decide +kernel
      have hl : raw26325step2Labels = raw26325step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26325step2 raw26325step2Labels = mixedMoment B raw26325step3 raw26325step3Labels := by
      have ha : raw26325step3 = raw26325step2 := by apply Matrix.ext; unfold raw26325step3 raw26325step2; decide +kernel
      have hl : raw26325step2Labels = labelEmbedding10 ∘ raw26325step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26325step2 raw26325step2Labels raw26325step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4424 node4424Labels := by rfl

def raw26326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26326step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26326step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26326step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw26326step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26326step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26326step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26326step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26326step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26326 raw26326Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw26326 raw26326Labels = mixedMoment B raw26326step0 raw26326step0Labels := by
      have hz : ∀ j, raw26326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26326step0 = (fun i j => raw26326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26326step0 raw26326; decide +kernel
      have hl : raw26326step0Labels = raw26326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26326 raw26326Labels permutation346 hz
    mixedMoment B raw26326step0 raw26326step0Labels = mixedMoment B raw26326step1 raw26326step1Labels := by
      have hz : ∀ j, raw26326step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26326step1 = (fun i j => raw26326step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26326step1 raw26326step0; decide +kernel
      have hl : raw26326step1Labels = raw26326step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26326step0 raw26326step0Labels permutation56 hz
    mixedMoment B raw26326step1 raw26326step1Labels = mixedMoment B raw26326step2 raw26326step2Labels := by
      have ha : raw26326step2 = (fun i j => raw26326step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26326step2 raw26326step1; decide +kernel
      have hl : raw26326step2Labels = raw26326step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26326step1 raw26326step1Labels permutation11 permutation7
    mixedMoment B raw26326step2 raw26326step2Labels = mixedMoment B raw26326step3 raw26326step3Labels := by
      have ha : raw26326step3 = -raw26326step2 := by apply Matrix.ext; change ∀ i j, raw26326step3 i j = -(raw26326step2 i j); unfold raw26326step3 raw26326step2; decide +kernel
      have hl : raw26326step3Labels = raw26326step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26326step3 raw26326step3Labels = mixedMoment B raw26326step4 raw26326step4Labels := by
      have ha : raw26326step4 = raw26326step3 := by apply Matrix.ext; unfold raw26326step4 raw26326step3; decide +kernel
      have hl : raw26326step3Labels = labelEmbedding10 ∘ raw26326step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26326step3 raw26326step3Labels raw26326step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

def raw26327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -1, -1]]
def raw26327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -1, -1]]
def raw26327step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26327step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![0, 1, -1], ![2, -1, -1]]
def raw26327step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26327step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw26327step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26327step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26327step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26327step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26327step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26327 raw26327Labels = mixedMoment B node4499 node4499Labels := by
  calc
    mixedMoment B raw26327 raw26327Labels = mixedMoment B raw26327step0 raw26327step0Labels := by
      have hz : ∀ j, raw26327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26327step0 = (fun i j => raw26327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26327step0 raw26327; decide +kernel
      have hl : raw26327step0Labels = raw26327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26327 raw26327Labels permutation346 hz
    mixedMoment B raw26327step0 raw26327step0Labels = mixedMoment B raw26327step1 raw26327step1Labels := by
      have hz : ∀ j, raw26327step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26327step1 = (fun i j => raw26327step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26327step1 raw26327step0; decide +kernel
      have hl : raw26327step1Labels = raw26327step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26327step0 raw26327step0Labels permutation56 hz
    mixedMoment B raw26327step1 raw26327step1Labels = mixedMoment B raw26327step2 raw26327step2Labels := by
      have ha : raw26327step2 = (fun i j => raw26327step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26327step2 raw26327step1; decide +kernel
      have hl : raw26327step2Labels = raw26327step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26327step1 raw26327step1Labels permutation11 permutation7
    mixedMoment B raw26327step2 raw26327step2Labels = mixedMoment B raw26327step3 raw26327step3Labels := by
      have ha : raw26327step3 = -raw26327step2 := by apply Matrix.ext; change ∀ i j, raw26327step3 i j = -(raw26327step2 i j); unfold raw26327step3 raw26327step2; decide +kernel
      have hl : raw26327step3Labels = raw26327step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26327step3 raw26327step3Labels = mixedMoment B raw26327step4 raw26327step4Labels := by
      have ha : raw26327step4 = raw26327step3 := by apply Matrix.ext; unfold raw26327step4 raw26327step3; decide +kernel
      have hl : raw26327step3Labels = labelEmbedding10 ∘ raw26327step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26327step3 raw26327step3Labels raw26327step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4499 node4499Labels := by rfl

def raw26328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26328step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26328step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26328step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26328step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26328step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26328step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26328step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26328step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26328step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26328 raw26328Labels = mixedMoment B node4502 node4502Labels := by
  calc
    mixedMoment B raw26328 raw26328Labels = mixedMoment B raw26328step0 raw26328step0Labels := by
      have hz : ∀ j, raw26328 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26328step0 = (fun i j => raw26328 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26328step0 raw26328; decide +kernel
      have hl : raw26328step0Labels = raw26328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26328 raw26328Labels permutation346 hz
    mixedMoment B raw26328step0 raw26328step0Labels = mixedMoment B raw26328step1 raw26328step1Labels := by
      have hz : ∀ j, raw26328step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26328step1 = (fun i j => raw26328step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26328step1 raw26328step0; decide +kernel
      have hl : raw26328step1Labels = raw26328step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26328step0 raw26328step0Labels permutation56 hz
    mixedMoment B raw26328step1 raw26328step1Labels = mixedMoment B raw26328step2 raw26328step2Labels := by
      have ha : raw26328step2 = (fun i j => raw26328step1 (permutation11 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26328step2 raw26328step1; decide +kernel
      have hl : raw26328step2Labels = raw26328step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26328step1 raw26328step1Labels permutation11 permutation7
    mixedMoment B raw26328step2 raw26328step2Labels = mixedMoment B raw26328step3 raw26328step3Labels := by
      have ha : raw26328step3 = -raw26328step2 := by apply Matrix.ext; change ∀ i j, raw26328step3 i j = -(raw26328step2 i j); unfold raw26328step3 raw26328step2; decide +kernel
      have hl : raw26328step3Labels = raw26328step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26328step3 raw26328step3Labels = mixedMoment B raw26328step4 raw26328step4Labels := by
      have ha : raw26328step4 = raw26328step3 := by apply Matrix.ext; unfold raw26328step4 raw26328step3; decide +kernel
      have hl : raw26328step3Labels = labelEmbedding10 ∘ raw26328step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26328step3 raw26328step3Labels raw26328step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4502 node4502Labels := by rfl

def raw26329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26329step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26329step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26329 raw26329Labels = mixedMoment B node4119 node4119Labels := by
  calc
    mixedMoment B raw26329 raw26329Labels = mixedMoment B raw26329step0 raw26329step0Labels := by
      have hz : ∀ j, raw26329 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26329step0 = (fun i j => raw26329 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26329step0 raw26329; decide +kernel
      have hl : raw26329step0Labels = raw26329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26329 raw26329Labels permutation346 hz
    mixedMoment B raw26329step0 raw26329step0Labels = mixedMoment B raw26329step1 raw26329step1Labels := by
      have ha : raw26329step1 = (fun i j => raw26329step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26329step1 raw26329step0; decide +kernel
      have hl : raw26329step1Labels = raw26329step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26329step0 raw26329step0Labels permutation34 permutation2
    _ = mixedMoment B node4119 node4119Labels := by rfl

def raw26330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26330step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26330step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26330 raw26330Labels = mixedMoment B node4210 node4210Labels := by
  calc
    mixedMoment B raw26330 raw26330Labels = mixedMoment B raw26330step0 raw26330step0Labels := by
      have ha : raw26330step0 = (fun i j => raw26330 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26330step0 raw26330; decide +kernel
      have hl : raw26330step0Labels = raw26330Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26330 raw26330Labels permutation178 permutation2
    _ = mixedMoment B node4210 node4210Labels := by rfl

def raw26331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26331step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw26331step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26331step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26331step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26331step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26331 raw26331Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw26331 raw26331Labels = mixedMoment B raw26331step0 raw26331step0Labels := by
      have hz : ∀ j, raw26331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26331step0 = (fun i j => raw26331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26331step0 raw26331; decide +kernel
      have hl : raw26331step0Labels = raw26331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26331 raw26331Labels permutation346 hz
    mixedMoment B raw26331step0 raw26331step0Labels = mixedMoment B raw26331step1 raw26331step1Labels := by
      have ha : raw26331step1 = (fun i j => raw26331step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26331step1 raw26331step0; decide +kernel
      have hl : raw26331step1Labels = raw26331step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26331step0 raw26331step0Labels permutation35 permutation7
    mixedMoment B raw26331step1 raw26331step1Labels = mixedMoment B raw26331step2 raw26331step2Labels := by
      have ha : raw26331step2 = -raw26331step1 := by apply Matrix.ext; change ∀ i j, raw26331step2 i j = -(raw26331step1 i j); unfold raw26331step2 raw26331step1; decide +kernel
      have hl : raw26331step2Labels = raw26331step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26331step2 raw26331step2Labels = mixedMoment B raw26331step3 raw26331step3Labels := by
      have ha : raw26331step3 = raw26331step2 := by apply Matrix.ext; unfold raw26331step3 raw26331step2; decide +kernel
      have hl : raw26331step2Labels = labelEmbedding10 ∘ raw26331step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26331step2 raw26331step2Labels raw26331step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4268 node4268Labels := by rfl

def raw26332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -1, -1]]
def raw26332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -1, -1]]
def raw26332step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26332step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26332 raw26332Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw26332 raw26332Labels = mixedMoment B raw26332step0 raw26332step0Labels := by
      have hz : ∀ j, raw26332 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26332step0 = (fun i j => raw26332 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26332step0 raw26332; decide +kernel
      have hl : raw26332step0Labels = raw26332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26332 raw26332Labels permutation346 hz
    mixedMoment B raw26332step0 raw26332step0Labels = mixedMoment B raw26332step1 raw26332step1Labels := by
      have ha : raw26332step1 = (fun i j => raw26332step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26332step1 raw26332step0; decide +kernel
      have hl : raw26332step1Labels = raw26332step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26332step0 raw26332step0Labels permutation44 permutation2
    _ = mixedMoment B node4265 node4265Labels := by rfl

def raw26333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26333step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26333step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26333step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26333step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26333step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26333step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26333 raw26333Labels = mixedMoment B node4267 node4267Labels := by
  calc
    mixedMoment B raw26333 raw26333Labels = mixedMoment B raw26333step0 raw26333step0Labels := by
      have hz : ∀ j, raw26333 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26333step0 = (fun i j => raw26333 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26333step0 raw26333; decide +kernel
      have hl : raw26333step0Labels = raw26333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26333 raw26333Labels permutation346 hz
    mixedMoment B raw26333step0 raw26333step0Labels = mixedMoment B raw26333step1 raw26333step1Labels := by
      have ha : raw26333step1 = (fun i j => raw26333step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26333step1 raw26333step0; decide +kernel
      have hl : raw26333step1Labels = raw26333step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26333step0 raw26333step0Labels permutation35 permutation7
    mixedMoment B raw26333step1 raw26333step1Labels = mixedMoment B raw26333step2 raw26333step2Labels := by
      have ha : raw26333step2 = -raw26333step1 := by apply Matrix.ext; change ∀ i j, raw26333step2 i j = -(raw26333step1 i j); unfold raw26333step2 raw26333step1; decide +kernel
      have hl : raw26333step2Labels = raw26333step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26333step2 raw26333step2Labels = mixedMoment B raw26333step3 raw26333step3Labels := by
      have ha : raw26333step3 = raw26333step2 := by apply Matrix.ext; unfold raw26333step3 raw26333step2; decide +kernel
      have hl : raw26333step2Labels = labelEmbedding10 ∘ raw26333step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26333step2 raw26333step2Labels raw26333step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4267 node4267Labels := by rfl

def raw26334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26334step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26334step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26334step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26334 raw26334Labels = mixedMoment B node4119 node4119Labels := by
  calc
    mixedMoment B raw26334 raw26334Labels = mixedMoment B raw26334step0 raw26334step0Labels := by
      have hz : ∀ j, raw26334 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26334step0 = (fun i j => raw26334 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26334step0 raw26334; decide +kernel
      have hl : raw26334step0Labels = raw26334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26334 raw26334Labels permutation265 hz
    mixedMoment B raw26334step0 raw26334step0Labels = mixedMoment B raw26334step1 raw26334step1Labels := by
      have ha : raw26334step1 = (fun i j => raw26334step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26334step1 raw26334step0; decide +kernel
      have hl : raw26334step1Labels = raw26334step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26334step0 raw26334step0Labels permutation34 permutation2
    _ = mixedMoment B node4119 node4119Labels := by rfl

def raw26335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26335step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26335 raw26335Labels = mixedMoment B node4210 node4210Labels := by
  calc
    mixedMoment B raw26335 raw26335Labels = mixedMoment B raw26335step0 raw26335step0Labels := by
      have ha : raw26335step0 = (fun i j => raw26335 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26335step0 raw26335; decide +kernel
      have hl : raw26335step0Labels = raw26335Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26335 raw26335Labels permutation154 permutation2
    _ = mixedMoment B node4210 node4210Labels := by rfl

def raw26336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26336Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26336step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw26336step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26336step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26336step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26336step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw26336step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26336 raw26336Labels = mixedMoment B node4268 node4268Labels := by
  calc
    mixedMoment B raw26336 raw26336Labels = mixedMoment B raw26336step0 raw26336step0Labels := by
      have hz : ∀ j, raw26336 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26336step0 = (fun i j => raw26336 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26336step0 raw26336; decide +kernel
      have hl : raw26336step0Labels = raw26336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26336 raw26336Labels permutation265 hz
    mixedMoment B raw26336step0 raw26336step0Labels = mixedMoment B raw26336step1 raw26336step1Labels := by
      have ha : raw26336step1 = (fun i j => raw26336step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26336step1 raw26336step0; decide +kernel
      have hl : raw26336step1Labels = raw26336step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26336step0 raw26336step0Labels permutation35 permutation7
    mixedMoment B raw26336step1 raw26336step1Labels = mixedMoment B raw26336step2 raw26336step2Labels := by
      have ha : raw26336step2 = -raw26336step1 := by apply Matrix.ext; change ∀ i j, raw26336step2 i j = -(raw26336step1 i j); unfold raw26336step2 raw26336step1; decide +kernel
      have hl : raw26336step2Labels = raw26336step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26336step2 raw26336step2Labels = mixedMoment B raw26336step3 raw26336step3Labels := by
      have ha : raw26336step3 = raw26336step2 := by apply Matrix.ext; unfold raw26336step3 raw26336step2; decide +kernel
      have hl : raw26336step2Labels = labelEmbedding10 ∘ raw26336step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26336step2 raw26336step2Labels raw26336step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4268 node4268Labels := by rfl

def raw26337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -1, -1]]
def raw26337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -1, -1]]
def raw26337step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26337step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw26337step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26337 raw26337Labels = mixedMoment B node4265 node4265Labels := by
  calc
    mixedMoment B raw26337 raw26337Labels = mixedMoment B raw26337step0 raw26337step0Labels := by
      have hz : ∀ j, raw26337 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26337step0 = (fun i j => raw26337 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26337step0 raw26337; decide +kernel
      have hl : raw26337step0Labels = raw26337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26337 raw26337Labels permutation265 hz
    mixedMoment B raw26337step0 raw26337step0Labels = mixedMoment B raw26337step1 raw26337step1Labels := by
      have ha : raw26337step1 = (fun i j => raw26337step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26337step1 raw26337step0; decide +kernel
      have hl : raw26337step1Labels = raw26337step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26337step0 raw26337step0Labels permutation44 permutation2
    _ = mixedMoment B node4265 node4265Labels := by rfl

def raw26338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26338step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw26338step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26338step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26338step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw26338step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw26338step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26338 raw26338Labels = mixedMoment B node4267 node4267Labels := by
  calc
    mixedMoment B raw26338 raw26338Labels = mixedMoment B raw26338step0 raw26338step0Labels := by
      have hz : ∀ j, raw26338 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26338step0 = (fun i j => raw26338 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26338step0 raw26338; decide +kernel
      have hl : raw26338step0Labels = raw26338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26338 raw26338Labels permutation265 hz
    mixedMoment B raw26338step0 raw26338step0Labels = mixedMoment B raw26338step1 raw26338step1Labels := by
      have ha : raw26338step1 = (fun i j => raw26338step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw26338step1 raw26338step0; decide +kernel
      have hl : raw26338step1Labels = raw26338step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26338step0 raw26338step0Labels permutation35 permutation7
    mixedMoment B raw26338step1 raw26338step1Labels = mixedMoment B raw26338step2 raw26338step2Labels := by
      have ha : raw26338step2 = -raw26338step1 := by apply Matrix.ext; change ∀ i j, raw26338step2 i j = -(raw26338step1 i j); unfold raw26338step2 raw26338step1; decide +kernel
      have hl : raw26338step2Labels = raw26338step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw26338step2 raw26338step2Labels = mixedMoment B raw26338step3 raw26338step3Labels := by
      have ha : raw26338step3 = raw26338step2 := by apply Matrix.ext; unfold raw26338step3 raw26338step2; decide +kernel
      have hl : raw26338step2Labels = labelEmbedding10 ∘ raw26338step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26338step2 raw26338step2Labels raw26338step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4267 node4267Labels := by rfl

def raw26339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26339step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26339step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![2, 0, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26339step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26339step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26339step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26339 raw26339Labels = mixedMoment B node4130 node4130Labels := by
  calc
    mixedMoment B raw26339 raw26339Labels = mixedMoment B raw26339step0 raw26339step0Labels := by
      have hz : ∀ j, raw26339 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26339step0 = (fun i j => raw26339 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26339step0 raw26339; decide +kernel
      have hl : raw26339step0Labels = raw26339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26339 raw26339Labels permutation346 hz
    mixedMoment B raw26339step0 raw26339step0Labels = mixedMoment B raw26339step1 raw26339step1Labels := by
      have hz : ∀ j, raw26339step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26339step1 = (fun i j => raw26339step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26339step1 raw26339step0; decide +kernel
      have hl : raw26339step1Labels = raw26339step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26339step0 raw26339step0Labels permutation56 hz
    mixedMoment B raw26339step1 raw26339step1Labels = mixedMoment B raw26339step2 raw26339step2Labels := by
      have ha : raw26339step2 = (fun i j => raw26339step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26339step2 raw26339step1; decide +kernel
      have hl : raw26339step2Labels = raw26339step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26339step1 raw26339step1Labels permutation11 permutation2
    _ = mixedMoment B node4130 node4130Labels := by rfl

def raw26340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26340step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26340step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26340 raw26340Labels = mixedMoment B node4221 node4221Labels := by
  calc
    mixedMoment B raw26340 raw26340Labels = mixedMoment B raw26340step0 raw26340step0Labels := by
      have hz : ∀ j, raw26340 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26340step0 = (fun i j => raw26340 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26340step0 raw26340; decide +kernel
      have hl : raw26340step0Labels = raw26340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26340 raw26340Labels permutation346 hz
    mixedMoment B raw26340step0 raw26340step0Labels = mixedMoment B raw26340step1 raw26340step1Labels := by
      have ha : raw26340step1 = (fun i j => raw26340step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26340step1 raw26340step0; decide +kernel
      have hl : raw26340step1Labels = raw26340step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26340step0 raw26340step0Labels permutation35 permutation2
    _ = mixedMoment B node4221 node4221Labels := by rfl

def raw26341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -1, -1]]
def raw26341step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26341step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26341 raw26341Labels = mixedMoment B node4221 node4221Labels := by
  calc
    mixedMoment B raw26341 raw26341Labels = mixedMoment B raw26341step0 raw26341step0Labels := by
      have hz : ∀ j, raw26341 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26341step0 = (fun i j => raw26341 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26341step0 raw26341; decide +kernel
      have hl : raw26341step0Labels = raw26341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26341 raw26341Labels permutation265 hz
    mixedMoment B raw26341step0 raw26341step0Labels = mixedMoment B raw26341step1 raw26341step1Labels := by
      have ha : raw26341step1 = (fun i j => raw26341step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26341step1 raw26341step0; decide +kernel
      have hl : raw26341step1Labels = raw26341step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26341step0 raw26341step0Labels permutation35 permutation2
    _ = mixedMoment B node4221 node4221Labels := by rfl

def raw26342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -1, -1]]
def raw26342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -1, -1]]
def raw26342step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26342step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![2, 0, -2], ![0, 1, -1], ![2, -1, -1]]
def raw26342step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26342step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw26342step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26342 raw26342Labels = mixedMoment B node4273 node4273Labels := by
  calc
    mixedMoment B raw26342 raw26342Labels = mixedMoment B raw26342step0 raw26342step0Labels := by
      have hz : ∀ j, raw26342 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26342step0 = (fun i j => raw26342 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26342step0 raw26342; decide +kernel
      have hl : raw26342step0Labels = raw26342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26342 raw26342Labels permutation346 hz
    mixedMoment B raw26342step0 raw26342step0Labels = mixedMoment B raw26342step1 raw26342step1Labels := by
      have hz : ∀ j, raw26342step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26342step1 = (fun i j => raw26342step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26342step1 raw26342step0; decide +kernel
      have hl : raw26342step1Labels = raw26342step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26342step0 raw26342step0Labels permutation56 hz
    mixedMoment B raw26342step1 raw26342step1Labels = mixedMoment B raw26342step2 raw26342step2Labels := by
      have ha : raw26342step2 = (fun i j => raw26342step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26342step2 raw26342step1; decide +kernel
      have hl : raw26342step2Labels = raw26342step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26342step1 raw26342step1Labels permutation11 permutation2
    _ = mixedMoment B node4273 node4273Labels := by rfl

def raw26343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26343step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26343step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![2, 0, -2], ![1, 0, -1], ![1, 0, -1]]
def raw26343step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26343step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![1, -1]]
def raw26343step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw26343step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw26343step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw26343step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw26343step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26343 raw26343Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw26343 raw26343Labels = mixedMoment B raw26343step0 raw26343step0Labels := by
      have hz : ∀ j, raw26343 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26343step0 = (fun i j => raw26343 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26343step0 raw26343; decide +kernel
      have hl : raw26343step0Labels = raw26343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26343 raw26343Labels permutation346 hz
    mixedMoment B raw26343step0 raw26343step0Labels = mixedMoment B raw26343step1 raw26343step1Labels := by
      have hz : ∀ j, raw26343step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26343step1 = (fun i j => raw26343step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26343step1 raw26343step0; decide +kernel
      have hl : raw26343step1Labels = raw26343step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26343step0 raw26343step0Labels permutation56 hz
    mixedMoment B raw26343step1 raw26343step1Labels = mixedMoment B raw26343step2 raw26343step2Labels := by
      have hz : ∀ i, raw26343step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw26343step2 = (fun i j => raw26343step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw26343step2 raw26343step1; decide +kernel
      have hl : raw26343step2Labels = (fun j => raw26343step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26343step1 raw26343step1Labels permutation4 hz
    mixedMoment B raw26343step2 raw26343step2Labels = mixedMoment B raw26343step3 raw26343step3Labels := by
      have ha : raw26343step3 = (fun i j => raw26343step2 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26343step3 raw26343step2; decide +kernel
      have hl : raw26343step3Labels = raw26343step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26343step2 raw26343step2Labels permutation11 permutation0
    mixedMoment B raw26343step3 raw26343step3Labels = mixedMoment B raw26343step4 raw26343step4Labels := by
      have ha : raw26343step4 = raw26343step3 := by apply Matrix.ext; unfold raw26343step4 raw26343step3; decide +kernel
      have hl : raw26343step3Labels = labelEmbedding2 ∘ raw26343step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw26343step3 raw26343step3Labels raw26343step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw26344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw26344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw26344step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26344step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw26344step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26344 raw26344Labels = mixedMoment B node4133 node4133Labels := by
  calc
    mixedMoment B raw26344 raw26344Labels = mixedMoment B raw26344step0 raw26344step0Labels := by
      have hz : ∀ j, raw26344 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26344step0 = (fun i j => raw26344 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26344step0 raw26344; decide +kernel
      have hl : raw26344step0Labels = raw26344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26344 raw26344Labels permutation346 hz
    mixedMoment B raw26344step0 raw26344step0Labels = mixedMoment B raw26344step1 raw26344step1Labels := by
      have hz : ∀ j, raw26344step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26344step1 = (fun i j => raw26344step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26344step1 raw26344step0; decide +kernel
      have hl : raw26344step1Labels = raw26344step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26344step0 raw26344step0Labels permutation56 hz
    _ = mixedMoment B node4133 node4133Labels := by rfl

def raw26345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw26345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw26345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26345 raw26345Labels = mixedMoment B node4224 node4224Labels := by
  calc
    mixedMoment B raw26345 raw26345Labels = mixedMoment B raw26345step0 raw26345step0Labels := by
      have hz : ∀ j, raw26345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26345step0 = (fun i j => raw26345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26345step0 raw26345; decide +kernel
      have hl : raw26345step0Labels = raw26345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26345 raw26345Labels permutation346 hz
    _ = mixedMoment B node4224 node4224Labels := by rfl

def raw26346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw26346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw26346step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26346 raw26346Labels = mixedMoment B node4224 node4224Labels := by
  calc
    mixedMoment B raw26346 raw26346Labels = mixedMoment B raw26346step0 raw26346step0Labels := by
      have hz : ∀ j, raw26346 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26346step0 = (fun i j => raw26346 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26346step0 raw26346; decide +kernel
      have hl : raw26346step0Labels = raw26346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26346 raw26346Labels permutation265 hz
    _ = mixedMoment B node4224 node4224Labels := by rfl

def raw26347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw26347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw26347step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26347step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw26347step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26347 raw26347Labels = mixedMoment B node4279 node4279Labels := by
  calc
    mixedMoment B raw26347 raw26347Labels = mixedMoment B raw26347step0 raw26347step0Labels := by
      have hz : ∀ j, raw26347 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26347step0 = (fun i j => raw26347 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26347step0 raw26347; decide +kernel
      have hl : raw26347step0Labels = raw26347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26347 raw26347Labels permutation346 hz
    mixedMoment B raw26347step0 raw26347step0Labels = mixedMoment B raw26347step1 raw26347step1Labels := by
      have hz : ∀ j, raw26347step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26347step1 = (fun i j => raw26347step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26347step1 raw26347step0; decide +kernel
      have hl : raw26347step1Labels = raw26347step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26347step0 raw26347step0Labels permutation56 hz
    _ = mixedMoment B node4279 node4279Labels := by rfl

def raw26348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, 0, -1]]
def raw26348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, 0, -1]]
def raw26348step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26348step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![2, -1, -1], ![1, 0, -1]]
def raw26348step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26348step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw26348step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26348 raw26348Labels = mixedMoment B node4283 node4283Labels := by
  calc
    mixedMoment B raw26348 raw26348Labels = mixedMoment B raw26348step0 raw26348step0Labels := by
      have hz : ∀ j, raw26348 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26348step0 = (fun i j => raw26348 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26348step0 raw26348; decide +kernel
      have hl : raw26348step0Labels = raw26348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26348 raw26348Labels permutation346 hz
    mixedMoment B raw26348step0 raw26348step0Labels = mixedMoment B raw26348step1 raw26348step1Labels := by
      have hz : ∀ j, raw26348step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26348step1 = (fun i j => raw26348step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26348step1 raw26348step0; decide +kernel
      have hl : raw26348step1Labels = raw26348step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26348step0 raw26348step0Labels permutation56 hz
    mixedMoment B raw26348step1 raw26348step1Labels = mixedMoment B raw26348step2 raw26348step2Labels := by
      have ha : raw26348step2 = (fun i j => raw26348step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26348step2 raw26348step1; decide +kernel
      have hl : raw26348step2Labels = raw26348step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26348step1 raw26348step1Labels permutation12 permutation2
    _ = mixedMoment B node4283 node4283Labels := by rfl

def raw26349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -2, -1]]
def raw26349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -2, -1]]
def raw26349step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26349step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 1, -2], ![1, 0, -1], ![3, -2, -1]]
def raw26349step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26349step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw26349step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26349 raw26349Labels = mixedMoment B node4128 node4128Labels := by
  calc
    mixedMoment B raw26349 raw26349Labels = mixedMoment B raw26349step0 raw26349step0Labels := by
      have hz : ∀ j, raw26349 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26349step0 = (fun i j => raw26349 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26349step0 raw26349; decide +kernel
      have hl : raw26349step0Labels = raw26349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26349 raw26349Labels permutation346 hz
    mixedMoment B raw26349step0 raw26349step0Labels = mixedMoment B raw26349step1 raw26349step1Labels := by
      have hz : ∀ j, raw26349step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26349step1 = (fun i j => raw26349step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26349step1 raw26349step0; decide +kernel
      have hl : raw26349step1Labels = raw26349step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26349step0 raw26349step0Labels permutation56 hz
    mixedMoment B raw26349step1 raw26349step1Labels = mixedMoment B raw26349step2 raw26349step2Labels := by
      have ha : raw26349step2 = (fun i j => raw26349step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26349step2 raw26349step1; decide +kernel
      have hl : raw26349step2Labels = raw26349step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26349step1 raw26349step1Labels permutation10 permutation2
    _ = mixedMoment B node4128 node4128Labels := by rfl

def raw26350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -2, -1]]
def raw26350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -2, -1]]
def raw26350step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw26350step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26350 raw26350Labels = mixedMoment B node4219 node4219Labels := by
  calc
    mixedMoment B raw26350 raw26350Labels = mixedMoment B raw26350step0 raw26350step0Labels := by
      have hz : ∀ j, raw26350 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26350step0 = (fun i j => raw26350 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26350step0 raw26350; decide +kernel
      have hl : raw26350step0Labels = raw26350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26350 raw26350Labels permutation346 hz
    mixedMoment B raw26350step0 raw26350step0Labels = mixedMoment B raw26350step1 raw26350step1Labels := by
      have ha : raw26350step1 = (fun i j => raw26350step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26350step1 raw26350step0; decide +kernel
      have hl : raw26350step1Labels = raw26350step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26350step0 raw26350step0Labels permutation34 permutation2
    _ = mixedMoment B node4219 node4219Labels := by rfl

def raw26351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -2, -1]]
def raw26351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -2, -1]]
def raw26351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw26351step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26351 raw26351Labels = mixedMoment B node4219 node4219Labels := by
  calc
    mixedMoment B raw26351 raw26351Labels = mixedMoment B raw26351step0 raw26351step0Labels := by
      have hz : ∀ j, raw26351 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26351step0 = (fun i j => raw26351 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26351step0 raw26351; decide +kernel
      have hl : raw26351step0Labels = raw26351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26351 raw26351Labels permutation265 hz
    mixedMoment B raw26351step0 raw26351step0Labels = mixedMoment B raw26351step1 raw26351step1Labels := by
      have ha : raw26351step1 = (fun i j => raw26351step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26351step1 raw26351step0; decide +kernel
      have hl : raw26351step1Labels = raw26351step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26351step0 raw26351step0Labels permutation34 permutation2
    _ = mixedMoment B node4219 node4219Labels := by rfl

def raw26352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw26352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw26352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26352step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw26352step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26352 raw26352Labels = mixedMoment B node4276 node4276Labels := by
  calc
    mixedMoment B raw26352 raw26352Labels = mixedMoment B raw26352step0 raw26352step0Labels := by
      have hz : ∀ j, raw26352 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26352step0 = (fun i j => raw26352 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26352step0 raw26352; decide +kernel
      have hl : raw26352step0Labels = raw26352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26352 raw26352Labels permutation346 hz
    mixedMoment B raw26352step0 raw26352step0Labels = mixedMoment B raw26352step1 raw26352step1Labels := by
      have hz : ∀ j, raw26352step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26352step1 = (fun i j => raw26352step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26352step1 raw26352step0; decide +kernel
      have hl : raw26352step1Labels = raw26352step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26352step0 raw26352step0Labels permutation56 hz
    _ = mixedMoment B node4276 node4276Labels := by rfl

def raw26353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -2, -1]]
def raw26353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -2, -1]]
def raw26353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26353step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 1, -1], ![3, -2, -1]]
def raw26353step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw26353step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw26353step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical26353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26353 raw26353Labels = mixedMoment B node4270 node4270Labels := by
  calc
    mixedMoment B raw26353 raw26353Labels = mixedMoment B raw26353step0 raw26353step0Labels := by
      have hz : ∀ j, raw26353 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26353step0 = (fun i j => raw26353 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26353step0 raw26353; decide +kernel
      have hl : raw26353step0Labels = raw26353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26353 raw26353Labels permutation346 hz
    mixedMoment B raw26353step0 raw26353step0Labels = mixedMoment B raw26353step1 raw26353step1Labels := by
      have hz : ∀ j, raw26353step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26353step1 = (fun i j => raw26353step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26353step1 raw26353step0; decide +kernel
      have hl : raw26353step1Labels = raw26353step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26353step0 raw26353step0Labels permutation56 hz
    mixedMoment B raw26353step1 raw26353step1Labels = mixedMoment B raw26353step2 raw26353step2Labels := by
      have ha : raw26353step2 = (fun i j => raw26353step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw26353step2 raw26353step1; decide +kernel
      have hl : raw26353step2Labels = raw26353step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26353step1 raw26353step1Labels permutation10 permutation2
    _ = mixedMoment B node4270 node4270Labels := by rfl

def raw26354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26354Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26354step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26354step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw26354step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26354 raw26354Labels = mixedMoment B node4057 node4057Labels := by
  calc
    mixedMoment B raw26354 raw26354Labels = mixedMoment B raw26354step0 raw26354step0Labels := by
      have hz : ∀ j, raw26354 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26354step0 = (fun i j => raw26354 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26354step0 raw26354; decide +kernel
      have hl : raw26354step0Labels = raw26354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26354 raw26354Labels permutation346 hz
    mixedMoment B raw26354step0 raw26354step0Labels = mixedMoment B raw26354step1 raw26354step1Labels := by
      have hz : ∀ i, raw26354step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26354step1 = (fun i j => raw26354step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26354step1 raw26354step0; decide +kernel
      have hl : raw26354step1Labels = (fun j => raw26354step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26354step0 raw26354step0Labels permutation6 hz
    _ = mixedMoment B node4057 node4057Labels := by rfl

def raw26355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26355Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26355step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw26355step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26355step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw26355step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26355 raw26355Labels = mixedMoment B node4063 node4063Labels := by
  calc
    mixedMoment B raw26355 raw26355Labels = mixedMoment B raw26355step0 raw26355step0Labels := by
      have hz : ∀ i, raw26355 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26355step0 = (fun i j => raw26355 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26355step0 raw26355; decide +kernel
      have hl : raw26355step0Labels = (fun j => raw26355Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26355 raw26355Labels permutation6 hz
    mixedMoment B raw26355step0 raw26355step0Labels = mixedMoment B raw26355step1 raw26355step1Labels := by
      have ha : raw26355step1 = (fun i j => raw26355step0 (permutation176 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26355step1 raw26355step0; decide +kernel
      have hl : raw26355step1Labels = raw26355step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26355step0 raw26355step0Labels permutation176 permutation0
    _ = mixedMoment B node4063 node4063Labels := by rfl

def raw26356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw26356Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26356step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26356step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26356step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26356step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw26356step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26356 raw26356Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw26356 raw26356Labels = mixedMoment B raw26356step0 raw26356step0Labels := by
      have hz : ∀ j, raw26356 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26356step0 = (fun i j => raw26356 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26356step0 raw26356; decide +kernel
      have hl : raw26356step0Labels = raw26356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26356 raw26356Labels permutation520 hz
    mixedMoment B raw26356step0 raw26356step0Labels = mixedMoment B raw26356step1 raw26356step1Labels := by
      have hz : ∀ j, raw26356step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw26356step1 = (fun i j => raw26356step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw26356step1 raw26356step0; decide +kernel
      have hl : raw26356step1Labels = raw26356step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26356step0 raw26356step0Labels permutation80 hz
    mixedMoment B raw26356step1 raw26356step1Labels = mixedMoment B raw26356step2 raw26356step2Labels := by
      have hz : ∀ i, raw26356step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26356step2 = (fun i j => raw26356step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26356step2 raw26356step1; decide +kernel
      have hl : raw26356step2Labels = (fun j => raw26356step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26356step1 raw26356step1Labels permutation6 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw26357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26357Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26357step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26357step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw26357step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26357 raw26357Labels = mixedMoment B node4057 node4057Labels := by
  calc
    mixedMoment B raw26357 raw26357Labels = mixedMoment B raw26357step0 raw26357step0Labels := by
      have hz : ∀ j, raw26357 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26357step0 = (fun i j => raw26357 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26357step0 raw26357; decide +kernel
      have hl : raw26357step0Labels = raw26357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26357 raw26357Labels permutation265 hz
    mixedMoment B raw26357step0 raw26357step0Labels = mixedMoment B raw26357step1 raw26357step1Labels := by
      have hz : ∀ i, raw26357step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26357step1 = (fun i j => raw26357step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26357step1 raw26357step0; decide +kernel
      have hl : raw26357step1Labels = (fun j => raw26357step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26357step0 raw26357step0Labels permutation6 hz
    _ = mixedMoment B node4057 node4057Labels := by rfl

def raw26358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26358Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26358step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw26358step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26358 raw26358Labels = mixedMoment B node4063 node4063Labels := by
  calc
    mixedMoment B raw26358 raw26358Labels = mixedMoment B raw26358step0 raw26358step0Labels := by
      have hz : ∀ i, raw26358 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26358step0 = (fun i j => raw26358 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26358step0 raw26358; decide +kernel
      have hl : raw26358step0Labels = (fun j => raw26358Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26358 raw26358Labels permutation6 hz
    _ = mixedMoment B node4063 node4063Labels := by rfl

def raw26359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw26359Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26359step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26359step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26359step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw26359step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26359 raw26359Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw26359 raw26359Labels = mixedMoment B raw26359step0 raw26359step0Labels := by
      have hz : ∀ j, raw26359 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26359step0 = (fun i j => raw26359 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26359step0 raw26359; decide +kernel
      have hl : raw26359step0Labels = raw26359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26359 raw26359Labels permutation520 hz
    mixedMoment B raw26359step0 raw26359step0Labels = mixedMoment B raw26359step1 raw26359step1Labels := by
      have hz : ∀ j, raw26359step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26359step1 = (fun i j => raw26359step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26359step1 raw26359step0; decide +kernel
      have hl : raw26359step1Labels = raw26359step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26359step0 raw26359step0Labels permutation56 hz
    mixedMoment B raw26359step1 raw26359step1Labels = mixedMoment B raw26359step2 raw26359step2Labels := by
      have hz : ∀ i, raw26359step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26359step2 = (fun i j => raw26359step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26359step2 raw26359step1; decide +kernel
      have hl : raw26359step2Labels = (fun j => raw26359step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26359step1 raw26359step1Labels permutation6 hz
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw26360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26360Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 5, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26360step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 5, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26360step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26360step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![2, -2], ![1, -1], ![2, -2]]
def raw26360step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26360step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-5, 5], ![1, -1], ![2, -2], ![2, -2]]
def raw26360step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26360 raw26360Labels = mixedMoment B node4059 node4059Labels := by
  calc
    mixedMoment B raw26360 raw26360Labels = mixedMoment B raw26360step0 raw26360step0Labels := by
      have hz : ∀ j, raw26360 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26360step0 = (fun i j => raw26360 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26360step0 raw26360; decide +kernel
      have hl : raw26360step0Labels = raw26360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26360 raw26360Labels permutation346 hz
    mixedMoment B raw26360step0 raw26360step0Labels = mixedMoment B raw26360step1 raw26360step1Labels := by
      have hz : ∀ j, raw26360step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw26360step1 = (fun i j => raw26360step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw26360step1 raw26360step0; decide +kernel
      have hl : raw26360step1Labels = raw26360step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26360step0 raw26360step0Labels permutation56 hz
    mixedMoment B raw26360step1 raw26360step1Labels = mixedMoment B raw26360step2 raw26360step2Labels := by
      have hz : ∀ i, raw26360step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26360step2 = (fun i j => raw26360step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26360step2 raw26360step1; decide +kernel
      have hl : raw26360step2Labels = (fun j => raw26360step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26360step1 raw26360step1Labels permutation6 hz
    mixedMoment B raw26360step2 raw26360step2Labels = mixedMoment B raw26360step3 raw26360step3Labels := by
      have ha : raw26360step3 = (fun i j => raw26360step2 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26360step3 raw26360step2; decide +kernel
      have hl : raw26360step3Labels = raw26360step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26360step2 raw26360step2Labels permutation10 permutation0
    _ = mixedMoment B node4059 node4059Labels := by rfl

def raw26361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26361step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26361step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![1, -1], ![2, -2]]
def raw26361step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26361step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw26361step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26361 raw26361Labels = mixedMoment B node4065 node4065Labels := by
  calc
    mixedMoment B raw26361 raw26361Labels = mixedMoment B raw26361step0 raw26361step0Labels := by
      have hz : ∀ j, raw26361 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw26361step0 = (fun i j => raw26361 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw26361step0 raw26361; decide +kernel
      have hl : raw26361step0Labels = raw26361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26361 raw26361Labels permutation346 hz
    mixedMoment B raw26361step0 raw26361step0Labels = mixedMoment B raw26361step1 raw26361step1Labels := by
      have hz : ∀ i, raw26361step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26361step1 = (fun i j => raw26361step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26361step1 raw26361step0; decide +kernel
      have hl : raw26361step1Labels = (fun j => raw26361step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26361step0 raw26361step0Labels permutation6 hz
    mixedMoment B raw26361step1 raw26361step1Labels = mixedMoment B raw26361step2 raw26361step2Labels := by
      have ha : raw26361step2 = (fun i j => raw26361step1 (permutation34 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26361step2 raw26361step1; decide +kernel
      have hl : raw26361step2Labels = raw26361step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26361step1 raw26361step1Labels permutation34 permutation0
    _ = mixedMoment B node4065 node4065Labels := by rfl

def raw26362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw26362step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26362step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![1, -1], ![2, -2]]
def raw26362step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw26362step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw26362step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26362 raw26362Labels = mixedMoment B node4065 node4065Labels := by
  calc
    mixedMoment B raw26362 raw26362Labels = mixedMoment B raw26362step0 raw26362step0Labels := by
      have hz : ∀ j, raw26362 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26362step0 = (fun i j => raw26362 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26362step0 raw26362; decide +kernel
      have hl : raw26362step0Labels = raw26362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26362 raw26362Labels permutation265 hz
    mixedMoment B raw26362step0 raw26362step0Labels = mixedMoment B raw26362step1 raw26362step1Labels := by
      have hz : ∀ i, raw26362step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26362step1 = (fun i j => raw26362step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26362step1 raw26362step0; decide +kernel
      have hl : raw26362step1Labels = (fun j => raw26362step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26362step0 raw26362step0Labels permutation6 hz
    mixedMoment B raw26362step1 raw26362step1Labels = mixedMoment B raw26362step2 raw26362step2Labels := by
      have ha : raw26362step2 = (fun i j => raw26362step1 (permutation34 i) (permutation0 j)) := by apply Matrix.ext; unfold raw26362step2 raw26362step1; decide +kernel
      have hl : raw26362step2Labels = raw26362step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26362step1 raw26362step1Labels permutation34 permutation0
    _ = mixedMoment B node4065 node4065Labels := by rfl

def raw26363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, -2, 0]]
def raw26363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw26363step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26363step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw26363step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26363step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 4, 0], ![2, -2, 0], ![2, -2, 0]]
def raw26363step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw26363step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw26363step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical26363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26363 raw26363Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw26363 raw26363Labels = mixedMoment B raw26363step0 raw26363step0Labels := by
      have hz : ∀ j, raw26363 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw26363step0 = (fun i j => raw26363 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw26363step0 raw26363; decide +kernel
      have hl : raw26363step0Labels = raw26363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26363 raw26363Labels permutation520 hz
    mixedMoment B raw26363step0 raw26363step0Labels = mixedMoment B raw26363step1 raw26363step1Labels := by
      have hz : ∀ j, raw26363step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw26363step1 = (fun i j => raw26363step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw26363step1 raw26363step0; decide +kernel
      have hl : raw26363step1Labels = raw26363step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26363step0 raw26363step0Labels permutation80 hz
    mixedMoment B raw26363step1 raw26363step1Labels = mixedMoment B raw26363step2 raw26363step2Labels := by
      have hz : ∀ j, raw26363step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw26363step2 = (fun i j => raw26363step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw26363step2 raw26363step1; decide +kernel
      have hl : raw26363step2Labels = raw26363step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26363step1 raw26363step1Labels permutation14 hz
    mixedMoment B raw26363step2 raw26363step2Labels = mixedMoment B raw26363step3 raw26363step3Labels := by
      have hz : ∀ i, raw26363step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw26363step3 = (fun i j => raw26363step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw26363step3 raw26363step2; decide +kernel
      have hl : raw26363step3Labels = (fun j => raw26363step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw26363step2 raw26363step2Labels permutation6 hz
    _ = mixedMoment B node4071 node4071Labels := by rfl

def raw26364 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26364Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw26364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26364step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw26364step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26364 raw26364Labels = mixedMoment B node1700 node1700Labels := by
  calc
    mixedMoment B raw26364 raw26364Labels = mixedMoment B raw26364step0 raw26364step0Labels := by
      have hz : ∀ j, raw26364 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26364step0 = (fun i j => raw26364 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26364step0 raw26364; decide +kernel
      have hl : raw26364step0Labels = raw26364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26364 raw26364Labels permutation265 hz
    mixedMoment B raw26364step0 raw26364step0Labels = mixedMoment B raw26364step1 raw26364step1Labels := by
      have ha : raw26364step1 = (fun i j => raw26364step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26364step1 raw26364step0; decide +kernel
      have hl : raw26364step1Labels = raw26364step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26364step0 raw26364step0Labels permutation32 permutation4
    mixedMoment B raw26364step1 raw26364step1Labels = mixedMoment B raw26364step2 raw26364step2Labels := by
      have ha : raw26364step2 = -raw26364step1 := by apply Matrix.ext; change ∀ i j, raw26364step2 i j = -(raw26364step1 i j); unfold raw26364step2 raw26364step1; decide +kernel
      have hl : raw26364step2Labels = raw26364step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1700 node1700Labels := by rfl

def raw26365 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26365Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26365step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw26365step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26365 raw26365Labels = mixedMoment B node3057 node3057Labels := by
  calc
    mixedMoment B raw26365 raw26365Labels = mixedMoment B raw26365step0 raw26365step0Labels := by
      have ha : raw26365step0 = (fun i j => raw26365 (permutation640 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26365step0 raw26365; decide +kernel
      have hl : raw26365step0Labels = raw26365Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26365 raw26365Labels permutation640 permutation4
    _ = mixedMoment B node3057 node3057Labels := by rfl

def raw26366 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26366Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26366step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw26366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26366 raw26366Labels = mixedMoment B node3072 node3072Labels := by
  calc
    mixedMoment B raw26366 raw26366Labels = mixedMoment B raw26366step0 raw26366step0Labels := by
      have hz : ∀ j, raw26366 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26366step0 = (fun i j => raw26366 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26366step0 raw26366; decide +kernel
      have hl : raw26366step0Labels = raw26366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26366 raw26366Labels permutation265 hz
    mixedMoment B raw26366step0 raw26366step0Labels = mixedMoment B raw26366step1 raw26366step1Labels := by
      have ha : raw26366step1 = (fun i j => raw26366step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26366step1 raw26366step0; decide +kernel
      have hl : raw26366step1Labels = raw26366step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26366step0 raw26366step0Labels permutation145 permutation4
    _ = mixedMoment B node3072 node3072Labels := by rfl

def raw26367 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26367Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1], ![2, -3, 1]]
def raw26367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw26367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw26367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical26367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw26367 raw26367Labels = mixedMoment B node3072 node3072Labels := by
  calc
    mixedMoment B raw26367 raw26367Labels = mixedMoment B raw26367step0 raw26367step0Labels := by
      have hz : ∀ j, raw26367 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw26367step0 = (fun i j => raw26367 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw26367step0 raw26367; decide +kernel
      have hl : raw26367step0Labels = raw26367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw26367 raw26367Labels permutation265 hz
    mixedMoment B raw26367step0 raw26367step0Labels = mixedMoment B raw26367step1 raw26367step1Labels := by
      have ha : raw26367step1 = (fun i j => raw26367step0 (permutation139 i) (permutation4 j)) := by apply Matrix.ext; unfold raw26367step1 raw26367step0; decide +kernel
      have hl : raw26367step1Labels = raw26367step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw26367step0 raw26367step0Labels permutation139 permutation4
    _ = mixedMoment B node3072 node3072Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
