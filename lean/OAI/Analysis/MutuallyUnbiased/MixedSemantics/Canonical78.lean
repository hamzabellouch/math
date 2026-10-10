import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw9984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9984Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9984step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9984step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw9984step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9984step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9984 raw9984Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw9984 raw9984Labels = mixedMoment B raw9984step0 raw9984step0Labels := by
      have hz : ∀ j, raw9984 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9984step0 = (fun i j => raw9984 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9984step0 raw9984; decide +kernel
      have hl : raw9984step0Labels = raw9984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9984 raw9984Labels permutation346 hz
    mixedMoment B raw9984step0 raw9984step0Labels = mixedMoment B raw9984step1 raw9984step1Labels := by
      have ha : raw9984step1 = (fun i j => raw9984step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9984step1 raw9984step0; decide +kernel
      have hl : raw9984step1Labels = raw9984step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9984step0 raw9984step0Labels permutation34 permutation3
    mixedMoment B raw9984step1 raw9984step1Labels = mixedMoment B raw9984step2 raw9984step2Labels := by
      have ha : raw9984step2 = raw9984step1 := by apply Matrix.ext; unfold raw9984step2 raw9984step1; decide +kernel
      have hl : raw9984step1Labels = labelEmbedding6 ∘ raw9984step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw9984step1 raw9984step1Labels raw9984step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4607 node4607Labels := by rfl

def raw9985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9985step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9985 raw9985Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw9985 raw9985Labels = mixedMoment B raw9985step0 raw9985step0Labels := by
      have hz : ∀ j, raw9985 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9985step0 = (fun i j => raw9985 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9985step0 raw9985; decide +kernel
      have hl : raw9985step0Labels = raw9985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9985 raw9985Labels permutation346 hz
    _ = mixedMoment B node5198 node5198Labels := by rfl

def raw9986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9986step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9986 raw9986Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw9986 raw9986Labels = mixedMoment B raw9986step0 raw9986step0Labels := by
      have ha : raw9986step0 = (fun i j => raw9986 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9986step0 raw9986; decide +kernel
      have hl : raw9986step0Labels = raw9986Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9986 raw9986Labels permutation176 permutation2
    _ = mixedMoment B node5144 node5144Labels := by rfl

def raw9987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw9987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw9987step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw9987step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9987 raw9987Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw9987 raw9987Labels = mixedMoment B raw9987step0 raw9987step0Labels := by
      have hz : ∀ j, raw9987 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9987step0 = (fun i j => raw9987 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9987step0 raw9987; decide +kernel
      have hl : raw9987step0Labels = raw9987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9987 raw9987Labels permutation520 hz
    mixedMoment B raw9987step0 raw9987step0Labels = mixedMoment B raw9987step1 raw9987step1Labels := by
      have hz : ∀ j, raw9987step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9987step1 = (fun i j => raw9987step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9987step1 raw9987step0; decide +kernel
      have hl : raw9987step1Labels = raw9987step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9987step0 raw9987step0Labels permutation80 hz
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw9988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw9988step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9988 raw9988Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw9988 raw9988Labels = mixedMoment B raw9988step0 raw9988step0Labels := by
      have hz : ∀ j, raw9988 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9988step0 = (fun i j => raw9988 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9988step0 raw9988; decide +kernel
      have hl : raw9988step0Labels = raw9988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9988 raw9988Labels permutation346 hz
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw9989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw9989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw9989step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9989step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9989 raw9989Labels = mixedMoment B node4592 node4592Labels := by
  calc
    mixedMoment B raw9989 raw9989Labels = mixedMoment B raw9989step0 raw9989step0Labels := by
      have hz : ∀ j, raw9989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9989step0 = (fun i j => raw9989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9989step0 raw9989; decide +kernel
      have hl : raw9989step0Labels = raw9989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9989 raw9989Labels permutation346 hz
    mixedMoment B raw9989step0 raw9989step0Labels = mixedMoment B raw9989step1 raw9989step1Labels := by
      have ha : raw9989step1 = (fun i j => raw9989step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9989step1 raw9989step0; decide +kernel
      have hl : raw9989step1Labels = raw9989step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9989step0 raw9989step0Labels permutation38 permutation2
    _ = mixedMoment B node4592 node4592Labels := by rfl

def raw9990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw9990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw9990step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9990 raw9990Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw9990 raw9990Labels = mixedMoment B raw9990step0 raw9990step0Labels := by
      have hz : ∀ j, raw9990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9990step0 = (fun i j => raw9990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9990step0 raw9990; decide +kernel
      have hl : raw9990step0Labels = raw9990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9990 raw9990Labels permutation346 hz
    _ = mixedMoment B node5188 node5188Labels := by rfl

def raw9991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw9991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9991step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9991step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9991 raw9991Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw9991 raw9991Labels = mixedMoment B raw9991step0 raw9991step0Labels := by
      have ha : raw9991step0 = (fun i j => raw9991 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9991step0 raw9991; decide +kernel
      have hl : raw9991step0Labels = raw9991Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9991 raw9991Labels permutation182 permutation2
    _ = mixedMoment B node5129 node5129Labels := by rfl

def raw9992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw9992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw9992step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw9992step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9992 raw9992Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw9992 raw9992Labels = mixedMoment B raw9992step0 raw9992step0Labels := by
      have hz : ∀ j, raw9992 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9992step0 = (fun i j => raw9992 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9992step0 raw9992; decide +kernel
      have hl : raw9992step0Labels = raw9992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9992 raw9992Labels permutation346 hz
    mixedMoment B raw9992step0 raw9992step0Labels = mixedMoment B raw9992step1 raw9992step1Labels := by
      have ha : raw9992step1 = (fun i j => raw9992step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9992step1 raw9992step0; decide +kernel
      have hl : raw9992step1Labels = raw9992step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9992step0 raw9992step0Labels permutation38 permutation2
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw9993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw9993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw9993step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw9993step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9993 raw9993Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw9993 raw9993Labels = mixedMoment B raw9993step0 raw9993step0Labels := by
      have hz : ∀ j, raw9993 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9993step0 = (fun i j => raw9993 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9993step0 raw9993; decide +kernel
      have hl : raw9993step0Labels = raw9993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9993 raw9993Labels permutation346 hz
    mixedMoment B raw9993step0 raw9993step0Labels = mixedMoment B raw9993step1 raw9993step1Labels := by
      have ha : raw9993step1 = (fun i j => raw9993step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9993step1 raw9993step0; decide +kernel
      have hl : raw9993step1Labels = raw9993step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9993step0 raw9993step0Labels permutation39 permutation2
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw9994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw9994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw9994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9994step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9994 raw9994Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw9994 raw9994Labels = mixedMoment B raw9994step0 raw9994step0Labels := by
      have hz : ∀ j, raw9994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9994step0 = (fun i j => raw9994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9994step0 raw9994; decide +kernel
      have hl : raw9994step0Labels = raw9994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9994 raw9994Labels permutation346 hz
    mixedMoment B raw9994step0 raw9994step0Labels = mixedMoment B raw9994step1 raw9994step1Labels := by
      have ha : raw9994step1 = (fun i j => raw9994step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9994step1 raw9994step0; decide +kernel
      have hl : raw9994step1Labels = raw9994step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9994step0 raw9994step0Labels permutation38 permutation2
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw9995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw9995Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw9995step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw9995step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw9995step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9995 raw9995Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw9995 raw9995Labels = mixedMoment B raw9995step0 raw9995step0Labels := by
      have hz : ∀ j, raw9995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9995step0 = (fun i j => raw9995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9995step0 raw9995; decide +kernel
      have hl : raw9995step0Labels = raw9995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9995 raw9995Labels permutation346 hz
    mixedMoment B raw9995step0 raw9995step0Labels = mixedMoment B raw9995step1 raw9995step1Labels := by
      have ha : raw9995step1 = (fun i j => raw9995step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9995step1 raw9995step0; decide +kernel
      have hl : raw9995step1Labels = raw9995step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9995step0 raw9995step0Labels permutation151 permutation2
    mixedMoment B raw9995step1 raw9995step1Labels = mixedMoment B raw9995step2 raw9995step2Labels := by
      have ha : raw9995step2 = -raw9995step1 := by apply Matrix.ext; change ∀ i j, raw9995step2 i j = -(raw9995step1 i j); unfold raw9995step2 raw9995step1; decide +kernel
      have hl : raw9995step2Labels = raw9995step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5147 node5147Labels := by rfl

def raw9996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw9996Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9996step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9996 raw9996Labels = mixedMoment B node5127 node5127Labels := by
  calc
    mixedMoment B raw9996 raw9996Labels = mixedMoment B raw9996step0 raw9996step0Labels := by
      have ha : raw9996step0 = (fun i j => raw9996 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9996step0 raw9996; decide +kernel
      have hl : raw9996step0Labels = raw9996Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9996 raw9996Labels permutation182 permutation2
    _ = mixedMoment B node5127 node5127Labels := by rfl

def raw9997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw9997Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw9997step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw9997step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9997 raw9997Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw9997 raw9997Labels = mixedMoment B raw9997step0 raw9997step0Labels := by
      have hz : ∀ j, raw9997 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9997step0 = (fun i j => raw9997 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9997step0 raw9997; decide +kernel
      have hl : raw9997step0Labels = raw9997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9997 raw9997Labels permutation346 hz
    mixedMoment B raw9997step0 raw9997step0Labels = mixedMoment B raw9997step1 raw9997step1Labels := by
      have ha : raw9997step1 = (fun i j => raw9997step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9997step1 raw9997step0; decide +kernel
      have hl : raw9997step1Labels = raw9997step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9997step0 raw9997step0Labels permutation38 permutation2
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw9998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw9998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw9998step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw9998step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw9998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw9998step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical9998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9998 raw9998Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw9998 raw9998Labels = mixedMoment B raw9998step0 raw9998step0Labels := by
      have hz : ∀ j, raw9998 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw9998step0 = (fun i j => raw9998 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw9998step0 raw9998; decide +kernel
      have hl : raw9998step0Labels = raw9998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9998 raw9998Labels permutation520 hz
    mixedMoment B raw9998step0 raw9998step0Labels = mixedMoment B raw9998step1 raw9998step1Labels := by
      have hz : ∀ j, raw9998step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw9998step1 = (fun i j => raw9998step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw9998step1 raw9998step0; decide +kernel
      have hl : raw9998step1Labels = raw9998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9998step0 raw9998step0Labels permutation80 hz
    mixedMoment B raw9998step1 raw9998step1Labels = mixedMoment B raw9998step2 raw9998step2Labels := by
      have ha : raw9998step2 = (fun i j => raw9998step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw9998step2 raw9998step1; decide +kernel
      have hl : raw9998step2Labels = raw9998step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9998step1 raw9998step1Labels permutation10 permutation2
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw9999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9999Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw9999step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw9999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw9999step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical9999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw9999 raw9999Labels = mixedMoment B node4027 node4027Labels := by
  calc
    mixedMoment B raw9999 raw9999Labels = mixedMoment B raw9999step0 raw9999step0Labels := by
      have hz : ∀ j, raw9999 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw9999step0 = (fun i j => raw9999 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw9999step0 raw9999; decide +kernel
      have hl : raw9999step0Labels = raw9999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw9999 raw9999Labels permutation346 hz
    mixedMoment B raw9999step0 raw9999step0Labels = mixedMoment B raw9999step1 raw9999step1Labels := by
      have ha : raw9999step1 = (fun i j => raw9999step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw9999step1 raw9999step0; decide +kernel
      have hl : raw9999step1Labels = raw9999step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw9999step0 raw9999step0Labels permutation32 permutation3
    _ = mixedMoment B node4027 node4027Labels := by rfl

def raw10000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10000Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10000 raw10000Labels = mixedMoment B node4032 node4032Labels := by
  calc
    mixedMoment B raw10000 raw10000Labels = mixedMoment B raw10000step0 raw10000step0Labels := by
      have ha : raw10000step0 = (fun i j => raw10000 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10000step0 raw10000; decide +kernel
      have hl : raw10000step0Labels = raw10000Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10000 raw10000Labels permutation176 permutation3
    _ = mixedMoment B node4032 node4032Labels := by rfl

def raw10001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10001Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10001step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw10001step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw10001step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10001 raw10001Labels = mixedMoment B node4035 node4035Labels := by
  calc
    mixedMoment B raw10001 raw10001Labels = mixedMoment B raw10001step0 raw10001step0Labels := by
      have hz : ∀ j, raw10001 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10001step0 = (fun i j => raw10001 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10001step0 raw10001; decide +kernel
      have hl : raw10001step0Labels = raw10001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10001 raw10001Labels permutation346 hz
    mixedMoment B raw10001step0 raw10001step0Labels = mixedMoment B raw10001step1 raw10001step1Labels := by
      have ha : raw10001step1 = (fun i j => raw10001step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10001step1 raw10001step0; decide +kernel
      have hl : raw10001step1Labels = raw10001step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10001step0 raw10001step0Labels permutation149 permutation3
    mixedMoment B raw10001step1 raw10001step1Labels = mixedMoment B raw10001step2 raw10001step2Labels := by
      have ha : raw10001step2 = -raw10001step1 := by apply Matrix.ext; change ∀ i j, raw10001step2 i j = -(raw10001step1 i j); unfold raw10001step2 raw10001step1; decide +kernel
      have hl : raw10001step2Labels = raw10001step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4035 node4035Labels := by rfl

def raw10002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw10002Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw10002step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw10002step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10002step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0]]
def raw10002step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10002 raw10002Labels = mixedMoment B node4037 node4037Labels := by
  calc
    mixedMoment B raw10002 raw10002Labels = mixedMoment B raw10002step0 raw10002step0Labels := by
      have hz : ∀ j, raw10002 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10002step0 = (fun i j => raw10002 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10002step0 raw10002; decide +kernel
      have hl : raw10002step0Labels = raw10002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10002 raw10002Labels permutation520 hz
    mixedMoment B raw10002step0 raw10002step0Labels = mixedMoment B raw10002step1 raw10002step1Labels := by
      have hz : ∀ j, raw10002step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10002step1 = (fun i j => raw10002step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10002step1 raw10002step0; decide +kernel
      have hl : raw10002step1Labels = raw10002step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10002step0 raw10002step0Labels permutation80 hz
    mixedMoment B raw10002step1 raw10002step1Labels = mixedMoment B raw10002step2 raw10002step2Labels := by
      have ha : raw10002step2 = (fun i j => raw10002step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10002step2 raw10002step1; decide +kernel
      have hl : raw10002step2Labels = raw10002step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10002step1 raw10002step1Labels permutation29 permutation6
    _ = mixedMoment B node4037 node4037Labels := by rfl

def raw10003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10003Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10003step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10003step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10003 raw10003Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw10003 raw10003Labels = mixedMoment B raw10003step0 raw10003step0Labels := by
      have hz : ∀ j, raw10003 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10003step0 = (fun i j => raw10003 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10003step0 raw10003; decide +kernel
      have hl : raw10003step0Labels = raw10003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10003 raw10003Labels permutation346 hz
    mixedMoment B raw10003step0 raw10003step0Labels = mixedMoment B raw10003step1 raw10003step1Labels := by
      have ha : raw10003step1 = (fun i j => raw10003step0 (permutation139 i) (permutation6 j)) := by apply Matrix.ext; unfold raw10003step1 raw10003step0; decide +kernel
      have hl : raw10003step1Labels = raw10003step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10003step0 raw10003step0Labels permutation139 permutation6
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw10004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10004Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10004step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10004step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10004 raw10004Labels = mixedMoment B node1267 node1267Labels := by
  calc
    mixedMoment B raw10004 raw10004Labels = mixedMoment B raw10004step0 raw10004step0Labels := by
      have hz : ∀ j, raw10004 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10004step0 = (fun i j => raw10004 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10004step0 raw10004; decide +kernel
      have hl : raw10004step0Labels = raw10004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10004 raw10004Labels permutation346 hz
    mixedMoment B raw10004step0 raw10004step0Labels = mixedMoment B raw10004step1 raw10004step1Labels := by
      have ha : raw10004step1 = (fun i j => raw10004step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10004step1 raw10004step0; decide +kernel
      have hl : raw10004step1Labels = raw10004step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10004step0 raw10004step0Labels permutation38 permutation3
    _ = mixedMoment B node1267 node1267Labels := by rfl

def raw10005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10005Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10005 raw10005Labels = mixedMoment B node2937 node2937Labels := by
  calc
    mixedMoment B raw10005 raw10005Labels = mixedMoment B raw10005step0 raw10005step0Labels := by
      have ha : raw10005step0 = (fun i j => raw10005 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10005step0 raw10005; decide +kernel
      have hl : raw10005step0Labels = raw10005Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10005 raw10005Labels permutation182 permutation3
    _ = mixedMoment B node2937 node2937Labels := by rfl

def raw10006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10006Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10006step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw10006step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10006 raw10006Labels = mixedMoment B node3001 node3001Labels := by
  calc
    mixedMoment B raw10006 raw10006Labels = mixedMoment B raw10006step0 raw10006step0Labels := by
      have hz : ∀ j, raw10006 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10006step0 = (fun i j => raw10006 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10006step0 raw10006; decide +kernel
      have hl : raw10006step0Labels = raw10006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10006 raw10006Labels permutation346 hz
    mixedMoment B raw10006step0 raw10006step0Labels = mixedMoment B raw10006step1 raw10006step1Labels := by
      have ha : raw10006step1 = (fun i j => raw10006step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10006step1 raw10006step0; decide +kernel
      have hl : raw10006step1Labels = raw10006step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10006step0 raw10006step0Labels permutation38 permutation3
    _ = mixedMoment B node3001 node3001Labels := by rfl

def raw10007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw10007Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw10007step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10007step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw10007step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10007step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw10007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10007 raw10007Labels = mixedMoment B node3112 node3112Labels := by
  calc
    mixedMoment B raw10007 raw10007Labels = mixedMoment B raw10007step0 raw10007step0Labels := by
      have hz : ∀ j, raw10007 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10007step0 = (fun i j => raw10007 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10007step0 raw10007; decide +kernel
      have hl : raw10007step0Labels = raw10007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10007 raw10007Labels permutation520 hz
    mixedMoment B raw10007step0 raw10007step0Labels = mixedMoment B raw10007step1 raw10007step1Labels := by
      have hz : ∀ j, raw10007step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10007step1 = (fun i j => raw10007step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10007step1 raw10007step0; decide +kernel
      have hl : raw10007step1Labels = raw10007step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10007step0 raw10007step0Labels permutation80 hz
    mixedMoment B raw10007step1 raw10007step1Labels = mixedMoment B raw10007step2 raw10007step2Labels := by
      have ha : raw10007step2 = (fun i j => raw10007step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10007step2 raw10007step1; decide +kernel
      have hl : raw10007step2Labels = raw10007step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10007step1 raw10007step1Labels permutation10 permutation3
    _ = mixedMoment B node3112 node3112Labels := by rfl

def raw10008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10008Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10008step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10008step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw10008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10008 raw10008Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw10008 raw10008Labels = mixedMoment B raw10008step0 raw10008step0Labels := by
      have hz : ∀ j, raw10008 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10008step0 = (fun i j => raw10008 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10008step0 raw10008; decide +kernel
      have hl : raw10008step0Labels = raw10008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10008 raw10008Labels permutation346 hz
    mixedMoment B raw10008step0 raw10008step0Labels = mixedMoment B raw10008step1 raw10008step1Labels := by
      have ha : raw10008step1 = (fun i j => raw10008step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10008step1 raw10008step0; decide +kernel
      have hl : raw10008step1Labels = raw10008step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10008step0 raw10008step0Labels permutation42 permutation3
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw10009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10009Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10009step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10009 raw10009Labels = mixedMoment B node1216 node1216Labels := by
  calc
    mixedMoment B raw10009 raw10009Labels = mixedMoment B raw10009step0 raw10009step0Labels := by
      have ha : raw10009step0 = (fun i j => raw10009 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10009step0 raw10009; decide +kernel
      have hl : raw10009step0Labels = raw10009Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10009 raw10009Labels permutation158 permutation3
    _ = mixedMoment B node1216 node1216Labels := by rfl

def raw10010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10010Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10010 raw10010Labels = mixedMoment B node2864 node2864Labels := by
  calc
    mixedMoment B raw10010 raw10010Labels = mixedMoment B raw10010step0 raw10010step0Labels := by
      have ha : raw10010step0 = (fun i j => raw10010 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10010step0 raw10010; decide +kernel
      have hl : raw10010step0Labels = raw10010Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10010 raw10010Labels permutation158 permutation3
    _ = mixedMoment B node2864 node2864Labels := by rfl

def raw10011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10011Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10011 raw10011Labels = mixedMoment B node2988 node2988Labels := by
  calc
    mixedMoment B raw10011 raw10011Labels = mixedMoment B raw10011step0 raw10011step0Labels := by
      have ha : raw10011step0 = (fun i j => raw10011 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10011step0 raw10011; decide +kernel
      have hl : raw10011step0Labels = raw10011Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10011 raw10011Labels permutation200 permutation3
    _ = mixedMoment B node2988 node2988Labels := by rfl

def raw10012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw10012Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw10012step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10012step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10012 raw10012Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw10012 raw10012Labels = mixedMoment B raw10012step0 raw10012step0Labels := by
      have hz : ∀ j, raw10012 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10012step0 = (fun i j => raw10012 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10012step0 raw10012; decide +kernel
      have hl : raw10012step0Labels = raw10012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10012 raw10012Labels permutation520 hz
    mixedMoment B raw10012step0 raw10012step0Labels = mixedMoment B raw10012step1 raw10012step1Labels := by
      have ha : raw10012step1 = (fun i j => raw10012step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10012step1 raw10012step0; decide +kernel
      have hl : raw10012step1Labels = raw10012step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10012step0 raw10012step0Labels permutation34 permutation3
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw10013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10013Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw10013step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10013 raw10013Labels = mixedMoment B node3085 node3085Labels := by
  calc
    mixedMoment B raw10013 raw10013Labels = mixedMoment B raw10013step0 raw10013step0Labels := by
      have ha : raw10013step0 = (fun i j => raw10013 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10013step0 raw10013; decide +kernel
      have hl : raw10013step0Labels = raw10013Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10013 raw10013Labels permutation162 permutation3
    _ = mixedMoment B node3085 node3085Labels := by rfl

def raw10014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10014Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10014step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10014step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10014 raw10014Labels = mixedMoment B node1241 node1241Labels := by
  calc
    mixedMoment B raw10014 raw10014Labels = mixedMoment B raw10014step0 raw10014step0Labels := by
      have hz : ∀ j, raw10014 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10014step0 = (fun i j => raw10014 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10014step0 raw10014; decide +kernel
      have hl : raw10014step0Labels = raw10014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10014 raw10014Labels permutation346 hz
    mixedMoment B raw10014step0 raw10014step0Labels = mixedMoment B raw10014step1 raw10014step1Labels := by
      have ha : raw10014step1 = (fun i j => raw10014step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10014step1 raw10014step0; decide +kernel
      have hl : raw10014step1Labels = raw10014step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10014step0 raw10014step0Labels permutation34 permutation3
    _ = mixedMoment B node1241 node1241Labels := by rfl

def raw10015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10015Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10015step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10015step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10015 raw10015Labels = mixedMoment B node2885 node2885Labels := by
  calc
    mixedMoment B raw10015 raw10015Labels = mixedMoment B raw10015step0 raw10015step0Labels := by
      have hz : ∀ j, raw10015 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10015step0 = (fun i j => raw10015 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10015step0 raw10015; decide +kernel
      have hl : raw10015step0Labels = raw10015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10015 raw10015Labels permutation346 hz
    mixedMoment B raw10015step0 raw10015step0Labels = mixedMoment B raw10015step1 raw10015step1Labels := by
      have ha : raw10015step1 = (fun i j => raw10015step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10015step1 raw10015step0; decide +kernel
      have hl : raw10015step1Labels = raw10015step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10015step0 raw10015step0Labels permutation34 permutation3
    _ = mixedMoment B node2885 node2885Labels := by rfl

def raw10016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10016Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10016step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw10016step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10016 raw10016Labels = mixedMoment B node2928 node2928Labels := by
  calc
    mixedMoment B raw10016 raw10016Labels = mixedMoment B raw10016step0 raw10016step0Labels := by
      have ha : raw10016step0 = (fun i j => raw10016 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10016step0 raw10016; decide +kernel
      have hl : raw10016step0Labels = raw10016Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10016 raw10016Labels permutation178 permutation3
    _ = mixedMoment B node2928 node2928Labels := by rfl

def raw10017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw10017Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw10017step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10017step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10017step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw10017step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10017 raw10017Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw10017 raw10017Labels = mixedMoment B raw10017step0 raw10017step0Labels := by
      have hz : ∀ j, raw10017 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10017step0 = (fun i j => raw10017 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10017step0 raw10017; decide +kernel
      have hl : raw10017step0Labels = raw10017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10017 raw10017Labels permutation520 hz
    mixedMoment B raw10017step0 raw10017step0Labels = mixedMoment B raw10017step1 raw10017step1Labels := by
      have hz : ∀ j, raw10017step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10017step1 = (fun i j => raw10017step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10017step1 raw10017step0; decide +kernel
      have hl : raw10017step1Labels = raw10017step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10017step0 raw10017step0Labels permutation80 hz
    mixedMoment B raw10017step1 raw10017step1Labels = mixedMoment B raw10017step2 raw10017step2Labels := by
      have ha : raw10017step2 = (fun i j => raw10017step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10017step2 raw10017step1; decide +kernel
      have hl : raw10017step2Labels = raw10017step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10017step1 raw10017step1Labels permutation8 permutation3
    _ = mixedMoment B node3103 node3103Labels := by rfl

def raw10018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10018Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10018step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw10018step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10018 raw10018Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw10018 raw10018Labels = mixedMoment B raw10018step0 raw10018step0Labels := by
      have hz : ∀ j, raw10018 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10018step0 = (fun i j => raw10018 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10018step0 raw10018; decide +kernel
      have hl : raw10018step0Labels = raw10018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10018 raw10018Labels permutation346 hz
    mixedMoment B raw10018step0 raw10018step0Labels = mixedMoment B raw10018step1 raw10018step1Labels := by
      have ha : raw10018step1 = (fun i j => raw10018step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10018step1 raw10018step0; decide +kernel
      have hl : raw10018step1Labels = raw10018step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10018step0 raw10018step0Labels permutation37 permutation3
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw10019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10019Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10019step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10019step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10019 raw10019Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw10019 raw10019Labels = mixedMoment B raw10019step0 raw10019step0Labels := by
      have hz : ∀ j, raw10019 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10019step0 = (fun i j => raw10019 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10019step0 raw10019; decide +kernel
      have hl : raw10019step0Labels = raw10019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10019 raw10019Labels permutation346 hz
    mixedMoment B raw10019step0 raw10019step0Labels = mixedMoment B raw10019step1 raw10019step1Labels := by
      have ha : raw10019step1 = (fun i j => raw10019step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10019step1 raw10019step0; decide +kernel
      have hl : raw10019step1Labels = raw10019step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10019step0 raw10019step0Labels permutation33 permutation3
    _ = mixedMoment B node1219 node1219Labels := by rfl

def raw10020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10020Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10020step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10020 raw10020Labels = mixedMoment B node2867 node2867Labels := by
  calc
    mixedMoment B raw10020 raw10020Labels = mixedMoment B raw10020step0 raw10020step0Labels := by
      have hz : ∀ j, raw10020 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10020step0 = (fun i j => raw10020 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10020step0 raw10020; decide +kernel
      have hl : raw10020step0Labels = raw10020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10020 raw10020Labels permutation346 hz
    mixedMoment B raw10020step0 raw10020step0Labels = mixedMoment B raw10020step1 raw10020step1Labels := by
      have ha : raw10020step1 = (fun i j => raw10020step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10020step1 raw10020step0; decide +kernel
      have hl : raw10020step1Labels = raw10020step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10020step0 raw10020step0Labels permutation33 permutation3
    _ = mixedMoment B node2867 node2867Labels := by rfl

def raw10021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10021Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10021 raw10021Labels = mixedMoment B node2916 node2916Labels := by
  calc
    mixedMoment B raw10021 raw10021Labels = mixedMoment B raw10021step0 raw10021step0Labels := by
      have ha : raw10021step0 = (fun i j => raw10021 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10021step0 raw10021; decide +kernel
      have hl : raw10021step0Labels = raw10021Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10021 raw10021Labels permutation177 permutation3
    _ = mixedMoment B node2916 node2916Labels := by rfl

def raw10022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10022Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10022step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10022step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10022 raw10022Labels = mixedMoment B node2990 node2990Labels := by
  calc
    mixedMoment B raw10022 raw10022Labels = mixedMoment B raw10022step0 raw10022step0Labels := by
      have hz : ∀ j, raw10022 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10022step0 = (fun i j => raw10022 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10022step0 raw10022; decide +kernel
      have hl : raw10022step0Labels = raw10022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10022 raw10022Labels permutation346 hz
    mixedMoment B raw10022step0 raw10022step0Labels = mixedMoment B raw10022step1 raw10022step1Labels := by
      have ha : raw10022step1 = (fun i j => raw10022step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10022step1 raw10022step0; decide +kernel
      have hl : raw10022step1Labels = raw10022step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10022step0 raw10022step0Labels permutation39 permutation3
    _ = mixedMoment B node2990 node2990Labels := by rfl

def raw10023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw10023Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw10023step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10023step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10023 raw10023Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw10023 raw10023Labels = mixedMoment B raw10023step0 raw10023step0Labels := by
      have hz : ∀ j, raw10023 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10023step0 = (fun i j => raw10023 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10023step0 raw10023; decide +kernel
      have hl : raw10023step0Labels = raw10023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10023 raw10023Labels permutation346 hz
    mixedMoment B raw10023step0 raw10023step0Labels = mixedMoment B raw10023step1 raw10023step1Labels := by
      have ha : raw10023step1 = (fun i j => raw10023step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10023step1 raw10023step0; decide +kernel
      have hl : raw10023step1Labels = raw10023step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10023step0 raw10023step0Labels permutation33 permutation3
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw10024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10024Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10024step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw10024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10024 raw10024Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw10024 raw10024Labels = mixedMoment B raw10024step0 raw10024step0Labels := by
      have hz : ∀ j, raw10024 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10024step0 = (fun i j => raw10024 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10024step0 raw10024; decide +kernel
      have hl : raw10024step0Labels = raw10024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10024 raw10024Labels permutation346 hz
    mixedMoment B raw10024step0 raw10024step0Labels = mixedMoment B raw10024step1 raw10024step1Labels := by
      have ha : raw10024step1 = (fun i j => raw10024step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10024step1 raw10024step0; decide +kernel
      have hl : raw10024step1Labels = raw10024step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10024step0 raw10024step0Labels permutation32 permutation3
    _ = mixedMoment B node1217 node1217Labels := by rfl

def raw10025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10025Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10025step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw10025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10025 raw10025Labels = mixedMoment B node2865 node2865Labels := by
  calc
    mixedMoment B raw10025 raw10025Labels = mixedMoment B raw10025step0 raw10025step0Labels := by
      have hz : ∀ j, raw10025 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10025step0 = (fun i j => raw10025 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10025step0 raw10025; decide +kernel
      have hl : raw10025step0Labels = raw10025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10025 raw10025Labels permutation346 hz
    mixedMoment B raw10025step0 raw10025step0Labels = mixedMoment B raw10025step1 raw10025step1Labels := by
      have ha : raw10025step1 = (fun i j => raw10025step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10025step1 raw10025step0; decide +kernel
      have hl : raw10025step1Labels = raw10025step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10025step0 raw10025step0Labels permutation32 permutation3
    _ = mixedMoment B node2865 node2865Labels := by rfl

def raw10026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10026Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw10026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10026 raw10026Labels = mixedMoment B node2914 node2914Labels := by
  calc
    mixedMoment B raw10026 raw10026Labels = mixedMoment B raw10026step0 raw10026step0Labels := by
      have ha : raw10026step0 = (fun i j => raw10026 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10026step0 raw10026; decide +kernel
      have hl : raw10026step0Labels = raw10026Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10026 raw10026Labels permutation176 permutation3
    _ = mixedMoment B node2914 node2914Labels := by rfl

def raw10027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10027Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10027step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw10027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw10027step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10027 raw10027Labels = mixedMoment B node2939 node2939Labels := by
  calc
    mixedMoment B raw10027 raw10027Labels = mixedMoment B raw10027step0 raw10027step0Labels := by
      have hz : ∀ j, raw10027 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10027step0 = (fun i j => raw10027 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10027step0 raw10027; decide +kernel
      have hl : raw10027step0Labels = raw10027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10027 raw10027Labels permutation346 hz
    mixedMoment B raw10027step0 raw10027step0Labels = mixedMoment B raw10027step1 raw10027step1Labels := by
      have ha : raw10027step1 = (fun i j => raw10027step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10027step1 raw10027step0; decide +kernel
      have hl : raw10027step1Labels = raw10027step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10027step0 raw10027step0Labels permutation149 permutation3
    mixedMoment B raw10027step1 raw10027step1Labels = mixedMoment B raw10027step2 raw10027step2Labels := by
      have ha : raw10027step2 = -raw10027step1 := by apply Matrix.ext; change ∀ i j, raw10027step2 i j = -(raw10027step1 i j); unfold raw10027step2 raw10027step1; decide +kernel
      have hl : raw10027step2Labels = raw10027step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2939 node2939Labels := by rfl

def raw10028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw10028Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw10028step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10028step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw10028step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw10028step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw10028step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10028 raw10028Labels = mixedMoment B node3090 node3090Labels := by
  calc
    mixedMoment B raw10028 raw10028Labels = mixedMoment B raw10028step0 raw10028step0Labels := by
      have hz : ∀ j, raw10028 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10028step0 = (fun i j => raw10028 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10028step0 raw10028; decide +kernel
      have hl : raw10028step0Labels = raw10028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10028 raw10028Labels permutation520 hz
    mixedMoment B raw10028step0 raw10028step0Labels = mixedMoment B raw10028step1 raw10028step1Labels := by
      have hz : ∀ j, raw10028step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10028step1 = (fun i j => raw10028step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10028step1 raw10028step0; decide +kernel
      have hl : raw10028step1Labels = raw10028step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10028step0 raw10028step0Labels permutation80 hz
    mixedMoment B raw10028step1 raw10028step1Labels = mixedMoment B raw10028step2 raw10028step2Labels := by
      have ha : raw10028step2 = (fun i j => raw10028step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10028step2 raw10028step1; decide +kernel
      have hl : raw10028step2Labels = raw10028step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10028step1 raw10028step1Labels permutation8 permutation3
    _ = mixedMoment B node3090 node3090Labels := by rfl

def raw10029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10029Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10029step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw10029step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10029step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10029step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10029step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10029step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10029 raw10029Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw10029 raw10029Labels = mixedMoment B raw10029step0 raw10029step0Labels := by
      have hz : ∀ j, raw10029 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10029step0 = (fun i j => raw10029 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10029step0 raw10029; decide +kernel
      have hl : raw10029step0Labels = raw10029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10029 raw10029Labels permutation346 hz
    mixedMoment B raw10029step0 raw10029step0Labels = mixedMoment B raw10029step1 raw10029step1Labels := by
      have ha : raw10029step1 = (fun i j => raw10029step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10029step1 raw10029step0; decide +kernel
      have hl : raw10029step1Labels = raw10029step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10029step0 raw10029step0Labels permutation40 permutation7
    mixedMoment B raw10029step1 raw10029step1Labels = mixedMoment B raw10029step2 raw10029step2Labels := by
      have ha : raw10029step2 = -raw10029step1 := by apply Matrix.ext; change ∀ i j, raw10029step2 i j = -(raw10029step1 i j); unfold raw10029step2 raw10029step1; decide +kernel
      have hl : raw10029step2Labels = raw10029step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10029step2 raw10029step2Labels = mixedMoment B raw10029step3 raw10029step3Labels := by
      have ha : raw10029step3 = raw10029step2 := by apply Matrix.ext; unfold raw10029step3 raw10029step2; decide +kernel
      have hl : raw10029step2Labels = labelEmbedding1 ∘ raw10029step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10029step2 raw10029step2Labels raw10029step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw10030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10030Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10030step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10030step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10030 raw10030Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw10030 raw10030Labels = mixedMoment B raw10030step0 raw10030step0Labels := by
      have ha : raw10030step0 = (fun i j => raw10030 (permutation620 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10030step0 raw10030; decide +kernel
      have hl : raw10030step0Labels = raw10030Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10030 raw10030Labels permutation620 permutation7
    mixedMoment B raw10030step0 raw10030step0Labels = mixedMoment B raw10030step1 raw10030step1Labels := by
      have ha : raw10030step1 = raw10030step0 := by apply Matrix.ext; unfold raw10030step1 raw10030step0; decide +kernel
      have hl : raw10030step0Labels = labelEmbedding1 ∘ raw10030step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10030step0 raw10030step0Labels raw10030step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3837 node3837Labels := by rfl

def raw10031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10031Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10031step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw10031step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10031step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10031step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10031step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10031 raw10031Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw10031 raw10031Labels = mixedMoment B raw10031step0 raw10031step0Labels := by
      have hz : ∀ j, raw10031 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10031step0 = (fun i j => raw10031 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10031step0 raw10031; decide +kernel
      have hl : raw10031step0Labels = raw10031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10031 raw10031Labels permutation346 hz
    mixedMoment B raw10031step0 raw10031step0Labels = mixedMoment B raw10031step1 raw10031step1Labels := by
      have ha : raw10031step1 = (fun i j => raw10031step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10031step1 raw10031step0; decide +kernel
      have hl : raw10031step1Labels = raw10031step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10031step0 raw10031step0Labels permutation40 permutation7
    mixedMoment B raw10031step1 raw10031step1Labels = mixedMoment B raw10031step2 raw10031step2Labels := by
      have ha : raw10031step2 = -raw10031step1 := by apply Matrix.ext; change ∀ i j, raw10031step2 i j = -(raw10031step1 i j); unfold raw10031step2 raw10031step1; decide +kernel
      have hl : raw10031step2Labels = raw10031step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10031step2 raw10031step2Labels = mixedMoment B raw10031step3 raw10031step3Labels := by
      have ha : raw10031step3 = raw10031step2 := by apply Matrix.ext; unfold raw10031step3 raw10031step2; decide +kernel
      have hl : raw10031step2Labels = labelEmbedding1 ∘ raw10031step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10031step2 raw10031step2Labels raw10031step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

def raw10032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw10032Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw10032step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10032step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw10032step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10032step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10032step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10032step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10032step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10032 raw10032Labels = mixedMoment B node3860 node3860Labels := by
  calc
    mixedMoment B raw10032 raw10032Labels = mixedMoment B raw10032step0 raw10032step0Labels := by
      have hz : ∀ j, raw10032 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10032step0 = (fun i j => raw10032 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10032step0 raw10032; decide +kernel
      have hl : raw10032step0Labels = raw10032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10032 raw10032Labels permutation520 hz
    mixedMoment B raw10032step0 raw10032step0Labels = mixedMoment B raw10032step1 raw10032step1Labels := by
      have hz : ∀ j, raw10032step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10032step1 = (fun i j => raw10032step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10032step1 raw10032step0; decide +kernel
      have hl : raw10032step1Labels = raw10032step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10032step0 raw10032step0Labels permutation80 hz
    mixedMoment B raw10032step1 raw10032step1Labels = mixedMoment B raw10032step2 raw10032step2Labels := by
      have ha : raw10032step2 = (fun i j => raw10032step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10032step2 raw10032step1; decide +kernel
      have hl : raw10032step2Labels = raw10032step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10032step1 raw10032step1Labels permutation29 permutation7
    mixedMoment B raw10032step2 raw10032step2Labels = mixedMoment B raw10032step3 raw10032step3Labels := by
      have ha : raw10032step3 = raw10032step2 := by apply Matrix.ext; unfold raw10032step3 raw10032step2; decide +kernel
      have hl : raw10032step2Labels = labelEmbedding1 ∘ raw10032step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10032step2 raw10032step2Labels raw10032step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3860 node3860Labels := by rfl

def raw10033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10033Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10033step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw10033step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10033step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10033step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10033step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10033step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10033 raw10033Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw10033 raw10033Labels = mixedMoment B raw10033step0 raw10033step0Labels := by
      have hz : ∀ j, raw10033 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10033step0 = (fun i j => raw10033 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10033step0 raw10033; decide +kernel
      have hl : raw10033step0Labels = raw10033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10033 raw10033Labels permutation346 hz
    mixedMoment B raw10033step0 raw10033step0Labels = mixedMoment B raw10033step1 raw10033step1Labels := by
      have ha : raw10033step1 = (fun i j => raw10033step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10033step1 raw10033step0; decide +kernel
      have hl : raw10033step1Labels = raw10033step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10033step0 raw10033step0Labels permutation40 permutation7
    mixedMoment B raw10033step1 raw10033step1Labels = mixedMoment B raw10033step2 raw10033step2Labels := by
      have ha : raw10033step2 = -raw10033step1 := by apply Matrix.ext; change ∀ i j, raw10033step2 i j = -(raw10033step1 i j); unfold raw10033step2 raw10033step1; decide +kernel
      have hl : raw10033step2Labels = raw10033step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10033step2 raw10033step2Labels = mixedMoment B raw10033step3 raw10033step3Labels := by
      have ha : raw10033step3 = raw10033step2 := by apply Matrix.ext; unfold raw10033step3 raw10033step2; decide +kernel
      have hl : raw10033step2Labels = labelEmbedding1 ∘ raw10033step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10033step2 raw10033step2Labels raw10033step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw10034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10034Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10034step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw10034step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10034step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10034step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10034step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10034step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10034 raw10034Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw10034 raw10034Labels = mixedMoment B raw10034step0 raw10034step0Labels := by
      have hz : ∀ j, raw10034 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10034step0 = (fun i j => raw10034 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10034step0 raw10034; decide +kernel
      have hl : raw10034step0Labels = raw10034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10034 raw10034Labels permutation346 hz
    mixedMoment B raw10034step0 raw10034step0Labels = mixedMoment B raw10034step1 raw10034step1Labels := by
      have ha : raw10034step1 = (fun i j => raw10034step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10034step1 raw10034step0; decide +kernel
      have hl : raw10034step1Labels = raw10034step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10034step0 raw10034step0Labels permutation40 permutation7
    mixedMoment B raw10034step1 raw10034step1Labels = mixedMoment B raw10034step2 raw10034step2Labels := by
      have ha : raw10034step2 = -raw10034step1 := by apply Matrix.ext; change ∀ i j, raw10034step2 i j = -(raw10034step1 i j); unfold raw10034step2 raw10034step1; decide +kernel
      have hl : raw10034step2Labels = raw10034step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10034step2 raw10034step2Labels = mixedMoment B raw10034step3 raw10034step3Labels := by
      have ha : raw10034step3 = raw10034step2 := by apply Matrix.ext; unfold raw10034step3 raw10034step2; decide +kernel
      have hl : raw10034step2Labels = labelEmbedding1 ∘ raw10034step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10034step2 raw10034step2Labels raw10034step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

def raw10035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10035Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw10035step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10035step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10035step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10035step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10035 raw10035Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw10035 raw10035Labels = mixedMoment B raw10035step0 raw10035step0Labels := by
      have ha : raw10035step0 = (fun i j => raw10035 (permutation208 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10035step0 raw10035; decide +kernel
      have hl : raw10035step0Labels = raw10035Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10035 raw10035Labels permutation208 permutation7
    mixedMoment B raw10035step0 raw10035step0Labels = mixedMoment B raw10035step1 raw10035step1Labels := by
      have ha : raw10035step1 = -raw10035step0 := by apply Matrix.ext; change ∀ i j, raw10035step1 i j = -(raw10035step0 i j); unfold raw10035step1 raw10035step0; decide +kernel
      have hl : raw10035step1Labels = raw10035step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10035step1 raw10035step1Labels = mixedMoment B raw10035step2 raw10035step2Labels := by
      have ha : raw10035step2 = raw10035step1 := by apply Matrix.ext; unfold raw10035step2 raw10035step1; decide +kernel
      have hl : raw10035step1Labels = labelEmbedding1 ∘ raw10035step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10035step1 raw10035step1Labels raw10035step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

def raw10036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10036Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10036step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw10036step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10036step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10036step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10036step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10036 raw10036Labels = mixedMoment B node3470 node3470Labels := by
  calc
    mixedMoment B raw10036 raw10036Labels = mixedMoment B raw10036step0 raw10036step0Labels := by
      have hz : ∀ j, raw10036 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10036step0 = (fun i j => raw10036 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10036step0 raw10036; decide +kernel
      have hl : raw10036step0Labels = raw10036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10036 raw10036Labels permutation346 hz
    mixedMoment B raw10036step0 raw10036step0Labels = mixedMoment B raw10036step1 raw10036step1Labels := by
      have ha : raw10036step1 = (fun i j => raw10036step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10036step1 raw10036step0; decide +kernel
      have hl : raw10036step1Labels = raw10036step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10036step0 raw10036step0Labels permutation40 permutation7
    mixedMoment B raw10036step1 raw10036step1Labels = mixedMoment B raw10036step2 raw10036step2Labels := by
      have ha : raw10036step2 = -raw10036step1 := by apply Matrix.ext; change ∀ i j, raw10036step2 i j = -(raw10036step1 i j); unfold raw10036step2 raw10036step1; decide +kernel
      have hl : raw10036step2Labels = raw10036step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10036step2 raw10036step2Labels = mixedMoment B raw10036step3 raw10036step3Labels := by
      have ha : raw10036step3 = raw10036step2 := by apply Matrix.ext; unfold raw10036step3 raw10036step2; decide +kernel
      have hl : raw10036step2Labels = labelEmbedding1 ∘ raw10036step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10036step2 raw10036step2Labels raw10036step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3470 node3470Labels := by rfl

def raw10037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw10037Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw10037step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10037step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw10037step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10037step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw10037step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10037step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10037step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10037step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10037step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10037 raw10037Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw10037 raw10037Labels = mixedMoment B raw10037step0 raw10037step0Labels := by
      have hz : ∀ j, raw10037 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10037step0 = (fun i j => raw10037 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10037step0 raw10037; decide +kernel
      have hl : raw10037step0Labels = raw10037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10037 raw10037Labels permutation520 hz
    mixedMoment B raw10037step0 raw10037step0Labels = mixedMoment B raw10037step1 raw10037step1Labels := by
      have hz : ∀ j, raw10037step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10037step1 = (fun i j => raw10037step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10037step1 raw10037step0; decide +kernel
      have hl : raw10037step1Labels = raw10037step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10037step0 raw10037step0Labels permutation80 hz
    mixedMoment B raw10037step1 raw10037step1Labels = mixedMoment B raw10037step2 raw10037step2Labels := by
      have ha : raw10037step2 = (fun i j => raw10037step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10037step2 raw10037step1; decide +kernel
      have hl : raw10037step2Labels = raw10037step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10037step1 raw10037step1Labels permutation10 permutation7
    mixedMoment B raw10037step2 raw10037step2Labels = mixedMoment B raw10037step3 raw10037step3Labels := by
      have ha : raw10037step3 = -raw10037step2 := by apply Matrix.ext; change ∀ i j, raw10037step3 i j = -(raw10037step2 i j); unfold raw10037step3 raw10037step2; decide +kernel
      have hl : raw10037step3Labels = raw10037step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10037step3 raw10037step3Labels = mixedMoment B raw10037step4 raw10037step4Labels := by
      have ha : raw10037step4 = raw10037step3 := by apply Matrix.ext; unfold raw10037step4 raw10037step3; decide +kernel
      have hl : raw10037step3Labels = labelEmbedding1 ∘ raw10037step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10037step3 raw10037step3Labels raw10037step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3547 node3547Labels := by rfl

def raw10038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10038Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10038step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10038step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10038step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10038step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10038step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10038step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10038step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10038 raw10038Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw10038 raw10038Labels = mixedMoment B raw10038step0 raw10038step0Labels := by
      have hz : ∀ j, raw10038 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10038step0 = (fun i j => raw10038 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10038step0 raw10038; decide +kernel
      have hl : raw10038step0Labels = raw10038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10038 raw10038Labels permutation346 hz
    mixedMoment B raw10038step0 raw10038step0Labels = mixedMoment B raw10038step1 raw10038step1Labels := by
      have ha : raw10038step1 = (fun i j => raw10038step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10038step1 raw10038step0; decide +kernel
      have hl : raw10038step1Labels = raw10038step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10038step0 raw10038step0Labels permutation40 permutation7
    mixedMoment B raw10038step1 raw10038step1Labels = mixedMoment B raw10038step2 raw10038step2Labels := by
      have ha : raw10038step2 = -raw10038step1 := by apply Matrix.ext; change ∀ i j, raw10038step2 i j = -(raw10038step1 i j); unfold raw10038step2 raw10038step1; decide +kernel
      have hl : raw10038step2Labels = raw10038step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10038step2 raw10038step2Labels = mixedMoment B raw10038step3 raw10038step3Labels := by
      have ha : raw10038step3 = raw10038step2 := by apply Matrix.ext; unfold raw10038step3 raw10038step2; decide +kernel
      have hl : raw10038step2Labels = labelEmbedding1 ∘ raw10038step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10038step2 raw10038step2Labels raw10038step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw10039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10039Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw10039step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10039step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10039step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10039step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10039 raw10039Labels = mixedMoment B node3288 node3288Labels := by
  calc
    mixedMoment B raw10039 raw10039Labels = mixedMoment B raw10039step0 raw10039step0Labels := by
      have ha : raw10039step0 = (fun i j => raw10039 (permutation208 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10039step0 raw10039; decide +kernel
      have hl : raw10039step0Labels = raw10039Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10039 raw10039Labels permutation208 permutation7
    mixedMoment B raw10039step0 raw10039step0Labels = mixedMoment B raw10039step1 raw10039step1Labels := by
      have ha : raw10039step1 = -raw10039step0 := by apply Matrix.ext; change ∀ i j, raw10039step1 i j = -(raw10039step0 i j); unfold raw10039step1 raw10039step0; decide +kernel
      have hl : raw10039step1Labels = raw10039step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10039step1 raw10039step1Labels = mixedMoment B raw10039step2 raw10039step2Labels := by
      have ha : raw10039step2 = raw10039step1 := by apply Matrix.ext; unfold raw10039step2 raw10039step1; decide +kernel
      have hl : raw10039step1Labels = labelEmbedding1 ∘ raw10039step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10039step1 raw10039step1Labels raw10039step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3288 node3288Labels := by rfl

def raw10040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10040Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw10040step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10040step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10040step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10040step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10040step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10040 raw10040Labels = mixedMoment B node3524 node3524Labels := by
  calc
    mixedMoment B raw10040 raw10040Labels = mixedMoment B raw10040step0 raw10040step0Labels := by
      have ha : raw10040step0 = (fun i j => raw10040 (permutation208 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10040step0 raw10040; decide +kernel
      have hl : raw10040step0Labels = raw10040Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10040 raw10040Labels permutation208 permutation7
    mixedMoment B raw10040step0 raw10040step0Labels = mixedMoment B raw10040step1 raw10040step1Labels := by
      have ha : raw10040step1 = -raw10040step0 := by apply Matrix.ext; change ∀ i j, raw10040step1 i j = -(raw10040step0 i j); unfold raw10040step1 raw10040step0; decide +kernel
      have hl : raw10040step1Labels = raw10040step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10040step1 raw10040step1Labels = mixedMoment B raw10040step2 raw10040step2Labels := by
      have ha : raw10040step2 = raw10040step1 := by apply Matrix.ext; unfold raw10040step2 raw10040step1; decide +kernel
      have hl : raw10040step1Labels = labelEmbedding1 ∘ raw10040step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10040step1 raw10040step1Labels raw10040step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3524 node3524Labels := by rfl

def raw10041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10041Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw10041step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10041step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10041step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10041step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10041step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10041 raw10041Labels = mixedMoment B node3459 node3459Labels := by
  calc
    mixedMoment B raw10041 raw10041Labels = mixedMoment B raw10041step0 raw10041step0Labels := by
      have ha : raw10041step0 = (fun i j => raw10041 (permutation208 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10041step0 raw10041; decide +kernel
      have hl : raw10041step0Labels = raw10041Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10041 raw10041Labels permutation208 permutation7
    mixedMoment B raw10041step0 raw10041step0Labels = mixedMoment B raw10041step1 raw10041step1Labels := by
      have ha : raw10041step1 = -raw10041step0 := by apply Matrix.ext; change ∀ i j, raw10041step1 i j = -(raw10041step0 i j); unfold raw10041step1 raw10041step0; decide +kernel
      have hl : raw10041step1Labels = raw10041step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10041step1 raw10041step1Labels = mixedMoment B raw10041step2 raw10041step2Labels := by
      have ha : raw10041step2 = raw10041step1 := by apply Matrix.ext; unfold raw10041step2 raw10041step1; decide +kernel
      have hl : raw10041step1Labels = labelEmbedding1 ∘ raw10041step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10041step1 raw10041step1Labels raw10041step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3459 node3459Labels := by rfl

def raw10042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw10042Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw10042step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw10042step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10042step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10042step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10042step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10042step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10042 raw10042Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw10042 raw10042Labels = mixedMoment B raw10042step0 raw10042step0Labels := by
      have hz : ∀ j, raw10042 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10042step0 = (fun i j => raw10042 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10042step0 raw10042; decide +kernel
      have hl : raw10042step0Labels = raw10042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10042 raw10042Labels permutation520 hz
    mixedMoment B raw10042step0 raw10042step0Labels = mixedMoment B raw10042step1 raw10042step1Labels := by
      have ha : raw10042step1 = (fun i j => raw10042step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10042step1 raw10042step0; decide +kernel
      have hl : raw10042step1Labels = raw10042step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10042step0 raw10042step0Labels permutation46 permutation7
    mixedMoment B raw10042step1 raw10042step1Labels = mixedMoment B raw10042step2 raw10042step2Labels := by
      have ha : raw10042step2 = -raw10042step1 := by apply Matrix.ext; change ∀ i j, raw10042step2 i j = -(raw10042step1 i j); unfold raw10042step2 raw10042step1; decide +kernel
      have hl : raw10042step2Labels = raw10042step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10042step2 raw10042step2Labels = mixedMoment B raw10042step3 raw10042step3Labels := by
      have ha : raw10042step3 = raw10042step2 := by apply Matrix.ext; unfold raw10042step3 raw10042step2; decide +kernel
      have hl : raw10042step2Labels = labelEmbedding1 ∘ raw10042step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10042step2 raw10042step2Labels raw10042step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw10043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10043Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw10043step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10043step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10043step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10043step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10043step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10043 raw10043Labels = mixedMoment B node3525 node3525Labels := by
  calc
    mixedMoment B raw10043 raw10043Labels = mixedMoment B raw10043step0 raw10043step0Labels := by
      have ha : raw10043step0 = (fun i j => raw10043 (permutation208 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10043step0 raw10043; decide +kernel
      have hl : raw10043step0Labels = raw10043Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10043 raw10043Labels permutation208 permutation7
    mixedMoment B raw10043step0 raw10043step0Labels = mixedMoment B raw10043step1 raw10043step1Labels := by
      have ha : raw10043step1 = -raw10043step0 := by apply Matrix.ext; change ∀ i j, raw10043step1 i j = -(raw10043step0 i j); unfold raw10043step1 raw10043step0; decide +kernel
      have hl : raw10043step1Labels = raw10043step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10043step1 raw10043step1Labels = mixedMoment B raw10043step2 raw10043step2Labels := by
      have ha : raw10043step2 = raw10043step1 := by apply Matrix.ext; unfold raw10043step2 raw10043step1; decide +kernel
      have hl : raw10043step1Labels = labelEmbedding1 ∘ raw10043step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10043step1 raw10043step1Labels raw10043step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3525 node3525Labels := by rfl

def raw10044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10044Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10044step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw10044step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10044step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10044step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10044step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw10044step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10044 raw10044Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw10044 raw10044Labels = mixedMoment B raw10044step0 raw10044step0Labels := by
      have hz : ∀ j, raw10044 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10044step0 = (fun i j => raw10044 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10044step0 raw10044; decide +kernel
      have hl : raw10044step0Labels = raw10044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10044 raw10044Labels permutation346 hz
    mixedMoment B raw10044step0 raw10044step0Labels = mixedMoment B raw10044step1 raw10044step1Labels := by
      have ha : raw10044step1 = (fun i j => raw10044step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10044step1 raw10044step0; decide +kernel
      have hl : raw10044step1Labels = raw10044step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10044step0 raw10044step0Labels permutation37 permutation5
    mixedMoment B raw10044step1 raw10044step1Labels = mixedMoment B raw10044step2 raw10044step2Labels := by
      have ha : raw10044step2 = -raw10044step1 := by apply Matrix.ext; change ∀ i j, raw10044step2 i j = -(raw10044step1 i j); unfold raw10044step2 raw10044step1; decide +kernel
      have hl : raw10044step2Labels = raw10044step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10044step2 raw10044step2Labels = mixedMoment B raw10044step3 raw10044step3Labels := by
      have ha : raw10044step3 = raw10044step2 := by apply Matrix.ext; unfold raw10044step3 raw10044step2; decide +kernel
      have hl : raw10044step2Labels = labelEmbedding1 ∘ raw10044step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10044step2 raw10044step2Labels raw10044step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

def raw10045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10045Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10045step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw10045step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10045step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10045step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10045step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10045step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10045 raw10045Labels = mixedMoment B node3570 node3570Labels := by
  calc
    mixedMoment B raw10045 raw10045Labels = mixedMoment B raw10045step0 raw10045step0Labels := by
      have hz : ∀ j, raw10045 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10045step0 = (fun i j => raw10045 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10045step0 raw10045; decide +kernel
      have hl : raw10045step0Labels = raw10045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10045 raw10045Labels permutation346 hz
    mixedMoment B raw10045step0 raw10045step0Labels = mixedMoment B raw10045step1 raw10045step1Labels := by
      have ha : raw10045step1 = (fun i j => raw10045step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10045step1 raw10045step0; decide +kernel
      have hl : raw10045step1Labels = raw10045step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10045step0 raw10045step0Labels permutation40 permutation7
    mixedMoment B raw10045step1 raw10045step1Labels = mixedMoment B raw10045step2 raw10045step2Labels := by
      have ha : raw10045step2 = -raw10045step1 := by apply Matrix.ext; change ∀ i j, raw10045step2 i j = -(raw10045step1 i j); unfold raw10045step2 raw10045step1; decide +kernel
      have hl : raw10045step2Labels = raw10045step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10045step2 raw10045step2Labels = mixedMoment B raw10045step3 raw10045step3Labels := by
      have ha : raw10045step3 = raw10045step2 := by apply Matrix.ext; unfold raw10045step3 raw10045step2; decide +kernel
      have hl : raw10045step2Labels = labelEmbedding1 ∘ raw10045step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10045step2 raw10045step2Labels raw10045step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3570 node3570Labels := by rfl

def raw10046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10046Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw10046step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10046step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10046step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10046step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10046 raw10046Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw10046 raw10046Labels = mixedMoment B raw10046step0 raw10046step0Labels := by
      have ha : raw10046step0 = (fun i j => raw10046 (permutation208 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10046step0 raw10046; decide +kernel
      have hl : raw10046step0Labels = raw10046Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10046 raw10046Labels permutation208 permutation7
    mixedMoment B raw10046step0 raw10046step0Labels = mixedMoment B raw10046step1 raw10046step1Labels := by
      have ha : raw10046step1 = -raw10046step0 := by apply Matrix.ext; change ∀ i j, raw10046step1 i j = -(raw10046step0 i j); unfold raw10046step1 raw10046step0; decide +kernel
      have hl : raw10046step1Labels = raw10046step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10046step1 raw10046step1Labels = mixedMoment B raw10046step2 raw10046step2Labels := by
      have ha : raw10046step2 = raw10046step1 := by apply Matrix.ext; unfold raw10046step2 raw10046step1; decide +kernel
      have hl : raw10046step1Labels = labelEmbedding1 ∘ raw10046step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10046step1 raw10046step1Labels raw10046step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

def raw10047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw10047Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw10047step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10047step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10047step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10047step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw10047step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10047step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10047step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10047step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10047step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10047 raw10047Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw10047 raw10047Labels = mixedMoment B raw10047step0 raw10047step0Labels := by
      have hz : ∀ j, raw10047 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10047step0 = (fun i j => raw10047 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10047step0 raw10047; decide +kernel
      have hl : raw10047step0Labels = raw10047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10047 raw10047Labels permutation520 hz
    mixedMoment B raw10047step0 raw10047step0Labels = mixedMoment B raw10047step1 raw10047step1Labels := by
      have hz : ∀ j, raw10047step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10047step1 = (fun i j => raw10047step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10047step1 raw10047step0; decide +kernel
      have hl : raw10047step1Labels = raw10047step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10047step0 raw10047step0Labels permutation80 hz
    mixedMoment B raw10047step1 raw10047step1Labels = mixedMoment B raw10047step2 raw10047step2Labels := by
      have ha : raw10047step2 = (fun i j => raw10047step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10047step2 raw10047step1; decide +kernel
      have hl : raw10047step2Labels = raw10047step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10047step1 raw10047step1Labels permutation10 permutation7
    mixedMoment B raw10047step2 raw10047step2Labels = mixedMoment B raw10047step3 raw10047step3Labels := by
      have ha : raw10047step3 = -raw10047step2 := by apply Matrix.ext; change ∀ i j, raw10047step3 i j = -(raw10047step2 i j); unfold raw10047step3 raw10047step2; decide +kernel
      have hl : raw10047step3Labels = raw10047step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10047step3 raw10047step3Labels = mixedMoment B raw10047step4 raw10047step4Labels := by
      have ha : raw10047step4 = raw10047step3 := by apply Matrix.ext; unfold raw10047step4 raw10047step3; decide +kernel
      have hl : raw10047step3Labels = labelEmbedding1 ∘ raw10047step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10047step3 raw10047step3Labels raw10047step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3582 node3582Labels := by rfl

def raw10048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10048Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10048step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw10048step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10048step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10048step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10048step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10048 raw10048Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw10048 raw10048Labels = mixedMoment B raw10048step0 raw10048step0Labels := by
      have hz : ∀ j, raw10048 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10048step0 = (fun i j => raw10048 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10048step0 raw10048; decide +kernel
      have hl : raw10048step0Labels = raw10048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10048 raw10048Labels permutation346 hz
    mixedMoment B raw10048step0 raw10048step0Labels = mixedMoment B raw10048step1 raw10048step1Labels := by
      have ha : raw10048step1 = (fun i j => raw10048step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10048step1 raw10048step0; decide +kernel
      have hl : raw10048step1Labels = raw10048step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10048step0 raw10048step0Labels permutation40 permutation7
    mixedMoment B raw10048step1 raw10048step1Labels = mixedMoment B raw10048step2 raw10048step2Labels := by
      have ha : raw10048step2 = -raw10048step1 := by apply Matrix.ext; change ∀ i j, raw10048step2 i j = -(raw10048step1 i j); unfold raw10048step2 raw10048step1; decide +kernel
      have hl : raw10048step2Labels = raw10048step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10048step2 raw10048step2Labels = mixedMoment B raw10048step3 raw10048step3Labels := by
      have ha : raw10048step3 = raw10048step2 := by apply Matrix.ext; unfold raw10048step3 raw10048step2; decide +kernel
      have hl : raw10048step2Labels = labelEmbedding1 ∘ raw10048step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10048step2 raw10048step2Labels raw10048step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw10049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10049Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10049step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw10049step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10049step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10049step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10049step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10049step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10049 raw10049Labels = mixedMoment B node3295 node3295Labels := by
  calc
    mixedMoment B raw10049 raw10049Labels = mixedMoment B raw10049step0 raw10049step0Labels := by
      have hz : ∀ j, raw10049 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10049step0 = (fun i j => raw10049 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10049step0 raw10049; decide +kernel
      have hl : raw10049step0Labels = raw10049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10049 raw10049Labels permutation346 hz
    mixedMoment B raw10049step0 raw10049step0Labels = mixedMoment B raw10049step1 raw10049step1Labels := by
      have ha : raw10049step1 = (fun i j => raw10049step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10049step1 raw10049step0; decide +kernel
      have hl : raw10049step1Labels = raw10049step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10049step0 raw10049step0Labels permutation36 permutation5
    mixedMoment B raw10049step1 raw10049step1Labels = mixedMoment B raw10049step2 raw10049step2Labels := by
      have ha : raw10049step2 = -raw10049step1 := by apply Matrix.ext; change ∀ i j, raw10049step2 i j = -(raw10049step1 i j); unfold raw10049step2 raw10049step1; decide +kernel
      have hl : raw10049step2Labels = raw10049step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10049step2 raw10049step2Labels = mixedMoment B raw10049step3 raw10049step3Labels := by
      have ha : raw10049step3 = raw10049step2 := by apply Matrix.ext; unfold raw10049step3 raw10049step2; decide +kernel
      have hl : raw10049step2Labels = labelEmbedding1 ∘ raw10049step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10049step2 raw10049step2Labels raw10049step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3295 node3295Labels := by rfl

def raw10050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10050Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10050step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw10050step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10050step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw10050step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10050step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw10050step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10050 raw10050Labels = mixedMoment B node3538 node3538Labels := by
  calc
    mixedMoment B raw10050 raw10050Labels = mixedMoment B raw10050step0 raw10050step0Labels := by
      have hz : ∀ j, raw10050 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10050step0 = (fun i j => raw10050 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10050step0 raw10050; decide +kernel
      have hl : raw10050step0Labels = raw10050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10050 raw10050Labels permutation346 hz
    mixedMoment B raw10050step0 raw10050step0Labels = mixedMoment B raw10050step1 raw10050step1Labels := by
      have ha : raw10050step1 = (fun i j => raw10050step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10050step1 raw10050step0; decide +kernel
      have hl : raw10050step1Labels = raw10050step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10050step0 raw10050step0Labels permutation40 permutation7
    mixedMoment B raw10050step1 raw10050step1Labels = mixedMoment B raw10050step2 raw10050step2Labels := by
      have ha : raw10050step2 = -raw10050step1 := by apply Matrix.ext; change ∀ i j, raw10050step2 i j = -(raw10050step1 i j); unfold raw10050step2 raw10050step1; decide +kernel
      have hl : raw10050step2Labels = raw10050step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10050step2 raw10050step2Labels = mixedMoment B raw10050step3 raw10050step3Labels := by
      have ha : raw10050step3 = raw10050step2 := by apply Matrix.ext; unfold raw10050step3 raw10050step2; decide +kernel
      have hl : raw10050step2Labels = labelEmbedding1 ∘ raw10050step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10050step2 raw10050step2Labels raw10050step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3538 node3538Labels := by rfl

def raw10051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10051Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw10051step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10051step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10051step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10051step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10051step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10051 raw10051Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw10051 raw10051Labels = mixedMoment B raw10051step0 raw10051step0Labels := by
      have ha : raw10051step0 = (fun i j => raw10051 (permutation208 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10051step0 raw10051; decide +kernel
      have hl : raw10051step0Labels = raw10051Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10051 raw10051Labels permutation208 permutation7
    mixedMoment B raw10051step0 raw10051step0Labels = mixedMoment B raw10051step1 raw10051step1Labels := by
      have ha : raw10051step1 = -raw10051step0 := by apply Matrix.ext; change ∀ i j, raw10051step1 i j = -(raw10051step0 i j); unfold raw10051step1 raw10051step0; decide +kernel
      have hl : raw10051step1Labels = raw10051step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10051step1 raw10051step1Labels = mixedMoment B raw10051step2 raw10051step2Labels := by
      have ha : raw10051step2 = raw10051step1 := by apply Matrix.ext; unfold raw10051step2 raw10051step1; decide +kernel
      have hl : raw10051step1Labels = labelEmbedding1 ∘ raw10051step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10051step1 raw10051step1Labels raw10051step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

def raw10052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10052Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10052step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw10052step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10052step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10052step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw10052step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10052 raw10052Labels = mixedMoment B node3478 node3478Labels := by
  calc
    mixedMoment B raw10052 raw10052Labels = mixedMoment B raw10052step0 raw10052step0Labels := by
      have hz : ∀ j, raw10052 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10052step0 = (fun i j => raw10052 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10052step0 raw10052; decide +kernel
      have hl : raw10052step0Labels = raw10052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10052 raw10052Labels permutation346 hz
    mixedMoment B raw10052step0 raw10052step0Labels = mixedMoment B raw10052step1 raw10052step1Labels := by
      have ha : raw10052step1 = (fun i j => raw10052step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10052step1 raw10052step0; decide +kernel
      have hl : raw10052step1Labels = raw10052step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10052step0 raw10052step0Labels permutation40 permutation7
    mixedMoment B raw10052step1 raw10052step1Labels = mixedMoment B raw10052step2 raw10052step2Labels := by
      have ha : raw10052step2 = -raw10052step1 := by apply Matrix.ext; change ∀ i j, raw10052step2 i j = -(raw10052step1 i j); unfold raw10052step2 raw10052step1; decide +kernel
      have hl : raw10052step2Labels = raw10052step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10052step2 raw10052step2Labels = mixedMoment B raw10052step3 raw10052step3Labels := by
      have ha : raw10052step3 = raw10052step2 := by apply Matrix.ext; unfold raw10052step3 raw10052step2; decide +kernel
      have hl : raw10052step2Labels = labelEmbedding1 ∘ raw10052step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10052step2 raw10052step2Labels raw10052step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3478 node3478Labels := by rfl

def raw10053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw10053Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw10053step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw10053step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10053step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10053step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10053step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw10053step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10053 raw10053Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw10053 raw10053Labels = mixedMoment B raw10053step0 raw10053step0Labels := by
      have hz : ∀ j, raw10053 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10053step0 = (fun i j => raw10053 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10053step0 raw10053; decide +kernel
      have hl : raw10053step0Labels = raw10053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10053 raw10053Labels permutation346 hz
    mixedMoment B raw10053step0 raw10053step0Labels = mixedMoment B raw10053step1 raw10053step1Labels := by
      have ha : raw10053step1 = (fun i j => raw10053step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10053step1 raw10053step0; decide +kernel
      have hl : raw10053step1Labels = raw10053step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10053step0 raw10053step0Labels permutation40 permutation7
    mixedMoment B raw10053step1 raw10053step1Labels = mixedMoment B raw10053step2 raw10053step2Labels := by
      have ha : raw10053step2 = -raw10053step1 := by apply Matrix.ext; change ∀ i j, raw10053step2 i j = -(raw10053step1 i j); unfold raw10053step2 raw10053step1; decide +kernel
      have hl : raw10053step2Labels = raw10053step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10053step2 raw10053step2Labels = mixedMoment B raw10053step3 raw10053step3Labels := by
      have ha : raw10053step3 = raw10053step2 := by apply Matrix.ext; unfold raw10053step3 raw10053step2; decide +kernel
      have hl : raw10053step2Labels = labelEmbedding1 ∘ raw10053step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10053step2 raw10053step2Labels raw10053step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw10054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10054Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10054step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw10054step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10054step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10054step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10054step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10054 raw10054Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw10054 raw10054Labels = mixedMoment B raw10054step0 raw10054step0Labels := by
      have hz : ∀ j, raw10054 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10054step0 = (fun i j => raw10054 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10054step0 raw10054; decide +kernel
      have hl : raw10054step0Labels = raw10054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10054 raw10054Labels permutation346 hz
    mixedMoment B raw10054step0 raw10054step0Labels = mixedMoment B raw10054step1 raw10054step1Labels := by
      have ha : raw10054step1 = (fun i j => raw10054step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10054step1 raw10054step0; decide +kernel
      have hl : raw10054step1Labels = raw10054step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10054step0 raw10054step0Labels permutation40 permutation7
    mixedMoment B raw10054step1 raw10054step1Labels = mixedMoment B raw10054step2 raw10054step2Labels := by
      have ha : raw10054step2 = -raw10054step1 := by apply Matrix.ext; change ∀ i j, raw10054step2 i j = -(raw10054step1 i j); unfold raw10054step2 raw10054step1; decide +kernel
      have hl : raw10054step2Labels = raw10054step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10054step2 raw10054step2Labels = mixedMoment B raw10054step3 raw10054step3Labels := by
      have ha : raw10054step3 = raw10054step2 := by apply Matrix.ext; unfold raw10054step3 raw10054step2; decide +kernel
      have hl : raw10054step2Labels = labelEmbedding1 ∘ raw10054step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10054step2 raw10054step2Labels raw10054step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3291 node3291Labels := by rfl

def raw10055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10055Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10055step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw10055step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10055step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10055step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10055step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw10055step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10055 raw10055Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw10055 raw10055Labels = mixedMoment B raw10055step0 raw10055step0Labels := by
      have hz : ∀ j, raw10055 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10055step0 = (fun i j => raw10055 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10055step0 raw10055; decide +kernel
      have hl : raw10055step0Labels = raw10055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10055 raw10055Labels permutation346 hz
    mixedMoment B raw10055step0 raw10055step0Labels = mixedMoment B raw10055step1 raw10055step1Labels := by
      have ha : raw10055step1 = (fun i j => raw10055step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10055step1 raw10055step0; decide +kernel
      have hl : raw10055step1Labels = raw10055step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10055step0 raw10055step0Labels permutation40 permutation7
    mixedMoment B raw10055step1 raw10055step1Labels = mixedMoment B raw10055step2 raw10055step2Labels := by
      have ha : raw10055step2 = -raw10055step1 := by apply Matrix.ext; change ∀ i j, raw10055step2 i j = -(raw10055step1 i j); unfold raw10055step2 raw10055step1; decide +kernel
      have hl : raw10055step2Labels = raw10055step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10055step2 raw10055step2Labels = mixedMoment B raw10055step3 raw10055step3Labels := by
      have ha : raw10055step3 = raw10055step2 := by apply Matrix.ext; unfold raw10055step3 raw10055step2; decide +kernel
      have hl : raw10055step2Labels = labelEmbedding1 ∘ raw10055step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10055step2 raw10055step2Labels raw10055step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

def raw10056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10056Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10056step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10056step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10056 raw10056Labels = mixedMoment B node3513 node3513Labels := by
  calc
    mixedMoment B raw10056 raw10056Labels = mixedMoment B raw10056step0 raw10056step0Labels := by
      have ha : raw10056step0 = (fun i j => raw10056 (permutation620 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10056step0 raw10056; decide +kernel
      have hl : raw10056step0Labels = raw10056Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10056 raw10056Labels permutation620 permutation7
    mixedMoment B raw10056step0 raw10056step0Labels = mixedMoment B raw10056step1 raw10056step1Labels := by
      have ha : raw10056step1 = raw10056step0 := by apply Matrix.ext; unfold raw10056step1 raw10056step0; decide +kernel
      have hl : raw10056step0Labels = labelEmbedding1 ∘ raw10056step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10056step0 raw10056step0Labels raw10056step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3513 node3513Labels := by rfl

def raw10057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10057Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10057step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw10057step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10057step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10057step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10057step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw10057step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10057 raw10057Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw10057 raw10057Labels = mixedMoment B raw10057step0 raw10057step0Labels := by
      have hz : ∀ j, raw10057 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10057step0 = (fun i j => raw10057 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10057step0 raw10057; decide +kernel
      have hl : raw10057step0Labels = raw10057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10057 raw10057Labels permutation346 hz
    mixedMoment B raw10057step0 raw10057step0Labels = mixedMoment B raw10057step1 raw10057step1Labels := by
      have ha : raw10057step1 = (fun i j => raw10057step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10057step1 raw10057step0; decide +kernel
      have hl : raw10057step1Labels = raw10057step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10057step0 raw10057step0Labels permutation40 permutation7
    mixedMoment B raw10057step1 raw10057step1Labels = mixedMoment B raw10057step2 raw10057step2Labels := by
      have ha : raw10057step2 = -raw10057step1 := by apply Matrix.ext; change ∀ i j, raw10057step2 i j = -(raw10057step1 i j); unfold raw10057step2 raw10057step1; decide +kernel
      have hl : raw10057step2Labels = raw10057step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10057step2 raw10057step2Labels = mixedMoment B raw10057step3 raw10057step3Labels := by
      have ha : raw10057step3 = raw10057step2 := by apply Matrix.ext; unfold raw10057step3 raw10057step2; decide +kernel
      have hl : raw10057step2Labels = labelEmbedding1 ∘ raw10057step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10057step2 raw10057step2Labels raw10057step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

def raw10058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw10058Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw10058step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10058step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw10058step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw10058step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10058step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw10058step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw10058step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10058 raw10058Labels = mixedMoment B node3545 node3545Labels := by
  calc
    mixedMoment B raw10058 raw10058Labels = mixedMoment B raw10058step0 raw10058step0Labels := by
      have hz : ∀ j, raw10058 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10058step0 = (fun i j => raw10058 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10058step0 raw10058; decide +kernel
      have hl : raw10058step0Labels = raw10058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10058 raw10058Labels permutation520 hz
    mixedMoment B raw10058step0 raw10058step0Labels = mixedMoment B raw10058step1 raw10058step1Labels := by
      have hz : ∀ j, raw10058step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10058step1 = (fun i j => raw10058step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10058step1 raw10058step0; decide +kernel
      have hl : raw10058step1Labels = raw10058step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10058step0 raw10058step0Labels permutation80 hz
    mixedMoment B raw10058step1 raw10058step1Labels = mixedMoment B raw10058step2 raw10058step2Labels := by
      have ha : raw10058step2 = (fun i j => raw10058step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw10058step2 raw10058step1; decide +kernel
      have hl : raw10058step2Labels = raw10058step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10058step1 raw10058step1Labels permutation29 permutation7
    mixedMoment B raw10058step2 raw10058step2Labels = mixedMoment B raw10058step3 raw10058step3Labels := by
      have ha : raw10058step3 = raw10058step2 := by apply Matrix.ext; unfold raw10058step3 raw10058step2; decide +kernel
      have hl : raw10058step2Labels = labelEmbedding1 ∘ raw10058step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10058step2 raw10058step2Labels raw10058step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3545 node3545Labels := by rfl

def raw10059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10059Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10059step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10059 raw10059Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw10059 raw10059Labels = mixedMoment B raw10059step0 raw10059step0Labels := by
      have hz : ∀ j, raw10059 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10059step0 = (fun i j => raw10059 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10059step0 raw10059; decide +kernel
      have hl : raw10059step0Labels = raw10059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10059 raw10059Labels permutation346 hz
    mixedMoment B raw10059step0 raw10059step0Labels = mixedMoment B raw10059step1 raw10059step1Labels := by
      have ha : raw10059step1 = (fun i j => raw10059step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10059step1 raw10059step0; decide +kernel
      have hl : raw10059step1Labels = raw10059step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10059step0 raw10059step0Labels permutation38 permutation2
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw10060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10060Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw10060step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10060step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw10060step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10060 raw10060Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw10060 raw10060Labels = mixedMoment B raw10060step0 raw10060step0Labels := by
      have hz : ∀ j, raw10060 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10060step0 = (fun i j => raw10060 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10060step0 raw10060; decide +kernel
      have hl : raw10060step0Labels = raw10060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10060 raw10060Labels permutation346 hz
    mixedMoment B raw10060step0 raw10060step0Labels = mixedMoment B raw10060step1 raw10060step1Labels := by
      have ha : raw10060step1 = (fun i j => raw10060step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10060step1 raw10060step0; decide +kernel
      have hl : raw10060step1Labels = raw10060step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10060step0 raw10060step0Labels permutation151 permutation2
    mixedMoment B raw10060step1 raw10060step1Labels = mixedMoment B raw10060step2 raw10060step2Labels := by
      have ha : raw10060step2 = -raw10060step1 := by apply Matrix.ext; change ∀ i j, raw10060step2 i j = -(raw10060step1 i j); unfold raw10060step2 raw10060step1; decide +kernel
      have hl : raw10060step2Labels = raw10060step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw10061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10061Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10061step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10061 raw10061Labels = mixedMoment B node3837 node3837Labels := by
  calc
    mixedMoment B raw10061 raw10061Labels = mixedMoment B raw10061step0 raw10061step0Labels := by
      have ha : raw10061step0 = (fun i j => raw10061 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10061step0 raw10061; decide +kernel
      have hl : raw10061step0Labels = raw10061Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10061 raw10061Labels permutation182 permutation2
    _ = mixedMoment B node3837 node3837Labels := by rfl

def raw10062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10062Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10062step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10062step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10062 raw10062Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw10062 raw10062Labels = mixedMoment B raw10062step0 raw10062step0Labels := by
      have hz : ∀ j, raw10062 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10062step0 = (fun i j => raw10062 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10062step0 raw10062; decide +kernel
      have hl : raw10062step0Labels = raw10062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10062 raw10062Labels permutation346 hz
    mixedMoment B raw10062step0 raw10062step0Labels = mixedMoment B raw10062step1 raw10062step1Labels := by
      have ha : raw10062step1 = (fun i j => raw10062step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10062step1 raw10062step0; decide +kernel
      have hl : raw10062step1Labels = raw10062step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10062step0 raw10062step0Labels permutation38 permutation2
    _ = mixedMoment B node3807 node3807Labels := by rfl

def raw10063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw10063Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw10063step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw10063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10063step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw10063step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10063 raw10063Labels = mixedMoment B node3905 node3905Labels := by
  calc
    mixedMoment B raw10063 raw10063Labels = mixedMoment B raw10063step0 raw10063step0Labels := by
      have hz : ∀ j, raw10063 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10063step0 = (fun i j => raw10063 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10063step0 raw10063; decide +kernel
      have hl : raw10063step0Labels = raw10063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10063 raw10063Labels permutation520 hz
    mixedMoment B raw10063step0 raw10063step0Labels = mixedMoment B raw10063step1 raw10063step1Labels := by
      have hz : ∀ j, raw10063step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10063step1 = (fun i j => raw10063step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10063step1 raw10063step0; decide +kernel
      have hl : raw10063step1Labels = raw10063step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10063step0 raw10063step0Labels permutation80 hz
    mixedMoment B raw10063step1 raw10063step1Labels = mixedMoment B raw10063step2 raw10063step2Labels := by
      have ha : raw10063step2 = (fun i j => raw10063step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10063step2 raw10063step1; decide +kernel
      have hl : raw10063step2Labels = raw10063step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10063step1 raw10063step1Labels permutation10 permutation2
    _ = mixedMoment B node3905 node3905Labels := by rfl

def raw10064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10064Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10064step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2]]
def raw10064step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10064 raw10064Labels = mixedMoment B node3903 node3903Labels := by
  calc
    mixedMoment B raw10064 raw10064Labels = mixedMoment B raw10064step0 raw10064step0Labels := by
      have hz : ∀ j, raw10064 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10064step0 = (fun i j => raw10064 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10064step0 raw10064; decide +kernel
      have hl : raw10064step0Labels = raw10064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10064 raw10064Labels permutation346 hz
    mixedMoment B raw10064step0 raw10064step0Labels = mixedMoment B raw10064step1 raw10064step1Labels := by
      have ha : raw10064step1 = (fun i j => raw10064step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10064step1 raw10064step0; decide +kernel
      have hl : raw10064step1Labels = raw10064step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10064step0 raw10064step0Labels permutation38 permutation2
    _ = mixedMoment B node3903 node3903Labels := by rfl

def raw10065 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-1, 1], ![0, 0], ![2, -2]]
def raw10065Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10065step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-1, 1], ![2, -2]]
def raw10065step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10065step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw10065step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw10065step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw10065step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical10065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10065 raw10065Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw10065 raw10065Labels = mixedMoment B raw10065step0 raw10065step0Labels := by
      have hz : ∀ j, raw10065 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10065step0 = (fun i j => raw10065 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10065step0 raw10065; decide +kernel
      have hl : raw10065step0Labels = raw10065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10065 raw10065Labels permutation520 hz
    mixedMoment B raw10065step0 raw10065step0Labels = mixedMoment B raw10065step1 raw10065step1Labels := by
      have hz : ∀ j, raw10065step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10065step1 = (fun i j => raw10065step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10065step1 raw10065step0; decide +kernel
      have hl : raw10065step1Labels = raw10065step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10065step0 raw10065step0Labels permutation80 hz
    mixedMoment B raw10065step1 raw10065step1Labels = mixedMoment B raw10065step2 raw10065step2Labels := by
      have ha : raw10065step2 = (fun i j => raw10065step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw10065step2 raw10065step1; decide +kernel
      have hl : raw10065step2Labels = raw10065step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10065step1 raw10065step1Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw10066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10066Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10066step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10066step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10066 raw10066Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw10066 raw10066Labels = mixedMoment B raw10066step0 raw10066step0Labels := by
      have hz : ∀ j, raw10066 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10066step0 = (fun i j => raw10066 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10066step0 raw10066; decide +kernel
      have hl : raw10066step0Labels = raw10066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10066 raw10066Labels permutation346 hz
    mixedMoment B raw10066step0 raw10066step0Labels = mixedMoment B raw10066step1 raw10066step1Labels := by
      have ha : raw10066step1 = (fun i j => raw10066step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10066step1 raw10066step0; decide +kernel
      have hl : raw10066step1Labels = raw10066step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10066step0 raw10066step0Labels permutation40 permutation2
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw10067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10067Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10067step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10067 raw10067Labels = mixedMoment B node1212 node1212Labels := by
  calc
    mixedMoment B raw10067 raw10067Labels = mixedMoment B raw10067step0 raw10067step0Labels := by
      have ha : raw10067step0 = (fun i j => raw10067 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10067step0 raw10067; decide +kernel
      have hl : raw10067step0Labels = raw10067Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10067 raw10067Labels permutation200 permutation2
    _ = mixedMoment B node1212 node1212Labels := by rfl

def raw10068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10068Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10068step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10068 raw10068Labels = mixedMoment B node1261 node1261Labels := by
  calc
    mixedMoment B raw10068 raw10068Labels = mixedMoment B raw10068step0 raw10068step0Labels := by
      have hz : ∀ j, raw10068 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10068step0 = (fun i j => raw10068 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10068step0 raw10068; decide +kernel
      have hl : raw10068step0Labels = raw10068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10068 raw10068Labels permutation346 hz
    _ = mixedMoment B node1261 node1261Labels := by rfl

def raw10069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10069Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10069step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10069step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10069step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10069 raw10069Labels = mixedMoment B node1219 node1219Labels := by
  calc
    mixedMoment B raw10069 raw10069Labels = mixedMoment B raw10069step0 raw10069step0Labels := by
      have hz : ∀ j, raw10069 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10069step0 = (fun i j => raw10069 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10069step0 raw10069; decide +kernel
      have hl : raw10069step0Labels = raw10069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10069 raw10069Labels permutation346 hz
    mixedMoment B raw10069step0 raw10069step0Labels = mixedMoment B raw10069step1 raw10069step1Labels := by
      have ha : raw10069step1 = (fun i j => raw10069step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10069step1 raw10069step0; decide +kernel
      have hl : raw10069step1Labels = raw10069step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10069step0 raw10069step0Labels permutation38 permutation2
    _ = mixedMoment B node1219 node1219Labels := by rfl

def raw10070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10070Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10070step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10070step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10070 raw10070Labels = mixedMoment B node1215 node1215Labels := by
  calc
    mixedMoment B raw10070 raw10070Labels = mixedMoment B raw10070step0 raw10070step0Labels := by
      have hz : ∀ j, raw10070 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10070step0 = (fun i j => raw10070 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10070step0 raw10070; decide +kernel
      have hl : raw10070step0Labels = raw10070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10070 raw10070Labels permutation346 hz
    mixedMoment B raw10070step0 raw10070step0Labels = mixedMoment B raw10070step1 raw10070step1Labels := by
      have ha : raw10070step1 = (fun i j => raw10070step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10070step1 raw10070step0; decide +kernel
      have hl : raw10070step1Labels = raw10070step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10070step0 raw10070step0Labels permutation38 permutation2
    _ = mixedMoment B node1215 node1215Labels := by rfl

def raw10071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10071Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10071step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10071 raw10071Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw10071 raw10071Labels = mixedMoment B raw10071step0 raw10071step0Labels := by
      have ha : raw10071step0 = (fun i j => raw10071 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10071step0 raw10071; decide +kernel
      have hl : raw10071step0Labels = raw10071Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10071 raw10071Labels permutation184 permutation2
    _ = mixedMoment B node2553 node2553Labels := by rfl

def raw10072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10072Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10072step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10072step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10072 raw10072Labels = mixedMoment B node2511 node2511Labels := by
  calc
    mixedMoment B raw10072 raw10072Labels = mixedMoment B raw10072step0 raw10072step0Labels := by
      have hz : ∀ j, raw10072 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10072step0 = (fun i j => raw10072 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10072step0 raw10072; decide +kernel
      have hl : raw10072step0Labels = raw10072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10072 raw10072Labels permutation346 hz
    mixedMoment B raw10072step0 raw10072step0Labels = mixedMoment B raw10072step1 raw10072step1Labels := by
      have ha : raw10072step1 = (fun i j => raw10072step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10072step1 raw10072step0; decide +kernel
      have hl : raw10072step1Labels = raw10072step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10072step0 raw10072step0Labels permutation40 permutation2
    _ = mixedMoment B node2511 node2511Labels := by rfl

def raw10073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw10073Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw10073step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10073step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw10073step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10073step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw10073step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10073 raw10073Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw10073 raw10073Labels = mixedMoment B raw10073step0 raw10073step0Labels := by
      have hz : ∀ j, raw10073 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10073step0 = (fun i j => raw10073 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10073step0 raw10073; decide +kernel
      have hl : raw10073step0Labels = raw10073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10073 raw10073Labels permutation520 hz
    mixedMoment B raw10073step0 raw10073step0Labels = mixedMoment B raw10073step1 raw10073step1Labels := by
      have hz : ∀ j, raw10073step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw10073step1 = (fun i j => raw10073step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw10073step1 raw10073step0; decide +kernel
      have hl : raw10073step1Labels = raw10073step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10073step0 raw10073step0Labels permutation80 hz
    mixedMoment B raw10073step1 raw10073step1Labels = mixedMoment B raw10073step2 raw10073step2Labels := by
      have ha : raw10073step2 = (fun i j => raw10073step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10073step2 raw10073step1; decide +kernel
      have hl : raw10073step2Labels = raw10073step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10073step1 raw10073step1Labels permutation10 permutation2
    _ = mixedMoment B node2742 node2742Labels := by rfl

def raw10074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10074 raw10074Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw10074 raw10074Labels = mixedMoment B raw10074step0 raw10074step0Labels := by
      have hz : ∀ j, raw10074 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10074step0 = (fun i j => raw10074 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10074step0 raw10074; decide +kernel
      have hl : raw10074step0Labels = raw10074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10074 raw10074Labels permutation346 hz
    mixedMoment B raw10074step0 raw10074step0Labels = mixedMoment B raw10074step1 raw10074step1Labels := by
      have ha : raw10074step1 = (fun i j => raw10074step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10074step1 raw10074step0; decide +kernel
      have hl : raw10074step1Labels = raw10074step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10074step0 raw10074step0Labels permutation40 permutation2
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw10075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10075Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10075step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10075 raw10075Labels = mixedMoment B node2614 node2614Labels := by
  calc
    mixedMoment B raw10075 raw10075Labels = mixedMoment B raw10075step0 raw10075step0Labels := by
      have ha : raw10075step0 = (fun i j => raw10075 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10075step0 raw10075; decide +kernel
      have hl : raw10075step0Labels = raw10075Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10075 raw10075Labels permutation158 permutation2
    _ = mixedMoment B node2614 node2614Labels := by rfl

def raw10076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10076Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10076 raw10076Labels = mixedMoment B node2632 node2632Labels := by
  calc
    mixedMoment B raw10076 raw10076Labels = mixedMoment B raw10076step0 raw10076step0Labels := by
      have hz : ∀ j, raw10076 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10076step0 = (fun i j => raw10076 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10076step0 raw10076; decide +kernel
      have hl : raw10076step0Labels = raw10076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10076 raw10076Labels permutation346 hz
    _ = mixedMoment B node2632 node2632Labels := by rfl

def raw10077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10077Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10077step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10077 raw10077Labels = mixedMoment B node2620 node2620Labels := by
  calc
    mixedMoment B raw10077 raw10077Labels = mixedMoment B raw10077step0 raw10077step0Labels := by
      have hz : ∀ j, raw10077 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10077step0 = (fun i j => raw10077 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10077step0 raw10077; decide +kernel
      have hl : raw10077step0Labels = raw10077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10077 raw10077Labels permutation346 hz
    _ = mixedMoment B node2620 node2620Labels := by rfl

def raw10078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10078Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10078step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw10078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw10078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10078 raw10078Labels = mixedMoment B node2569 node2569Labels := by
  calc
    mixedMoment B raw10078 raw10078Labels = mixedMoment B raw10078step0 raw10078step0Labels := by
      have hz : ∀ j, raw10078 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10078step0 = (fun i j => raw10078 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10078step0 raw10078; decide +kernel
      have hl : raw10078step0Labels = raw10078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10078 raw10078Labels permutation346 hz
    mixedMoment B raw10078step0 raw10078step0Labels = mixedMoment B raw10078step1 raw10078step1Labels := by
      have ha : raw10078step1 = (fun i j => raw10078step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10078step1 raw10078step0; decide +kernel
      have hl : raw10078step1Labels = raw10078step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10078step0 raw10078step0Labels permutation151 permutation2
    mixedMoment B raw10078step1 raw10078step1Labels = mixedMoment B raw10078step2 raw10078step2Labels := by
      have ha : raw10078step2 = -raw10078step1 := by apply Matrix.ext; change ∀ i j, raw10078step2 i j = -(raw10078step1 i j); unfold raw10078step2 raw10078step1; decide +kernel
      have hl : raw10078step2Labels = raw10078step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2569 node2569Labels := by rfl

def raw10079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10079Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10079step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10079 raw10079Labels = mixedMoment B node2479 node2479Labels := by
  calc
    mixedMoment B raw10079 raw10079Labels = mixedMoment B raw10079step0 raw10079step0Labels := by
      have ha : raw10079step0 = (fun i j => raw10079 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10079step0 raw10079; decide +kernel
      have hl : raw10079step0Labels = raw10079Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10079 raw10079Labels permutation200 permutation2
    _ = mixedMoment B node2479 node2479Labels := by rfl

def raw10080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw10080Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw10080step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10080step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10080 raw10080Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw10080 raw10080Labels = mixedMoment B raw10080step0 raw10080step0Labels := by
      have hz : ∀ j, raw10080 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw10080step0 = (fun i j => raw10080 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw10080step0 raw10080; decide +kernel
      have hl : raw10080step0Labels = raw10080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10080 raw10080Labels permutation520 hz
    mixedMoment B raw10080step0 raw10080step0Labels = mixedMoment B raw10080step1 raw10080step1Labels := by
      have ha : raw10080step1 = (fun i j => raw10080step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10080step1 raw10080step0; decide +kernel
      have hl : raw10080step1Labels = raw10080step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10080step0 raw10080step0Labels permutation44 permutation2
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw10081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw10081Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10081 raw10081Labels = mixedMoment B node2720 node2720Labels := by
  calc
    mixedMoment B raw10081 raw10081Labels = mixedMoment B raw10081step0 raw10081step0Labels := by
      have ha : raw10081step0 = (fun i j => raw10081 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10081step0 raw10081; decide +kernel
      have hl : raw10081step0Labels = raw10081Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10081 raw10081Labels permutation200 permutation2
    _ = mixedMoment B node2720 node2720Labels := by rfl

def raw10082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10082Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw10082step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10082 raw10082Labels = mixedMoment B node2566 node2566Labels := by
  calc
    mixedMoment B raw10082 raw10082Labels = mixedMoment B raw10082step0 raw10082step0Labels := by
      have ha : raw10082step0 = (fun i j => raw10082 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10082step0 raw10082; decide +kernel
      have hl : raw10082step0Labels = raw10082Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10082 raw10082Labels permutation176 permutation2
    _ = mixedMoment B node2566 node2566Labels := by rfl

def raw10083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw10083Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10083step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw10083step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10083 raw10083Labels = mixedMoment B node2545 node2545Labels := by
  calc
    mixedMoment B raw10083 raw10083Labels = mixedMoment B raw10083step0 raw10083step0Labels := by
      have ha : raw10083step0 = (fun i j => raw10083 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10083step0 raw10083; decide +kernel
      have hl : raw10083step0Labels = raw10083Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10083 raw10083Labels permutation182 permutation2
    _ = mixedMoment B node2545 node2545Labels := by rfl

def raw10084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw10084Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw10084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10084step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical10084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10084 raw10084Labels = mixedMoment B node2542 node2542Labels := by
  calc
    mixedMoment B raw10084 raw10084Labels = mixedMoment B raw10084step0 raw10084step0Labels := by
      have ha : raw10084step0 = (fun i j => raw10084 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10084step0 raw10084; decide +kernel
      have hl : raw10084step0Labels = raw10084Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10084 raw10084Labels permutation182 permutation2
    _ = mixedMoment B node2542 node2542Labels := by rfl

def raw10085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10085step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw10085step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10085step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10085step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10085step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw10085step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10085 raw10085Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw10085 raw10085Labels = mixedMoment B raw10085step0 raw10085step0Labels := by
      have hz : ∀ j, raw10085 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10085step0 = (fun i j => raw10085 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10085step0 raw10085; decide +kernel
      have hl : raw10085step0Labels = raw10085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10085 raw10085Labels permutation346 hz
    mixedMoment B raw10085step0 raw10085step0Labels = mixedMoment B raw10085step1 raw10085step1Labels := by
      have ha : raw10085step1 = (fun i j => raw10085step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10085step1 raw10085step0; decide +kernel
      have hl : raw10085step1Labels = raw10085step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10085step0 raw10085step0Labels permutation151 permutation3
    mixedMoment B raw10085step1 raw10085step1Labels = mixedMoment B raw10085step2 raw10085step2Labels := by
      have ha : raw10085step2 = -raw10085step1 := by apply Matrix.ext; change ∀ i j, raw10085step2 i j = -(raw10085step1 i j); unfold raw10085step2 raw10085step1; decide +kernel
      have hl : raw10085step2Labels = raw10085step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10085step2 raw10085step2Labels = mixedMoment B raw10085step3 raw10085step3Labels := by
      have ha : raw10085step3 = raw10085step2 := by apply Matrix.ext; unfold raw10085step3 raw10085step2; decide +kernel
      have hl : raw10085step2Labels = labelEmbedding6 ∘ raw10085step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10085step2 raw10085step2Labels raw10085step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw10086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw10086step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10086step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10086step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10086step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10086 raw10086Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw10086 raw10086Labels = mixedMoment B raw10086step0 raw10086step0Labels := by
      have ha : raw10086step0 = (fun i j => raw10086 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10086step0 raw10086; decide +kernel
      have hl : raw10086step0Labels = raw10086Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10086 raw10086Labels permutation676 permutation3
    mixedMoment B raw10086step0 raw10086step0Labels = mixedMoment B raw10086step1 raw10086step1Labels := by
      have ha : raw10086step1 = -raw10086step0 := by apply Matrix.ext; change ∀ i j, raw10086step1 i j = -(raw10086step0 i j); unfold raw10086step1 raw10086step0; decide +kernel
      have hl : raw10086step1Labels = raw10086step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10086step1 raw10086step1Labels = mixedMoment B raw10086step2 raw10086step2Labels := by
      have ha : raw10086step2 = raw10086step1 := by apply Matrix.ext; unfold raw10086step2 raw10086step1; decide +kernel
      have hl : raw10086step1Labels = labelEmbedding6 ∘ raw10086step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10086step1 raw10086step1Labels raw10086step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw10087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw10087step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10087step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10087step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw10087step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10087 raw10087Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw10087 raw10087Labels = mixedMoment B raw10087step0 raw10087step0Labels := by
      have hz : ∀ j, raw10087 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10087step0 = (fun i j => raw10087 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10087step0 raw10087; decide +kernel
      have hl : raw10087step0Labels = raw10087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10087 raw10087Labels permutation346 hz
    mixedMoment B raw10087step0 raw10087step0Labels = mixedMoment B raw10087step1 raw10087step1Labels := by
      have ha : raw10087step1 = (fun i j => raw10087step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10087step1 raw10087step0; decide +kernel
      have hl : raw10087step1Labels = raw10087step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10087step0 raw10087step0Labels permutation149 permutation3
    mixedMoment B raw10087step1 raw10087step1Labels = mixedMoment B raw10087step2 raw10087step2Labels := by
      have ha : raw10087step2 = -raw10087step1 := by apply Matrix.ext; change ∀ i j, raw10087step2 i j = -(raw10087step1 i j); unfold raw10087step2 raw10087step1; decide +kernel
      have hl : raw10087step2Labels = raw10087step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10087step2 raw10087step2Labels = mixedMoment B raw10087step3 raw10087step3Labels := by
      have ha : raw10087step3 = raw10087step2 := by apply Matrix.ext; unfold raw10087step3 raw10087step2; decide +kernel
      have hl : raw10087step2Labels = labelEmbedding6 ∘ raw10087step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10087step2 raw10087step2Labels raw10087step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw10088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10088step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10088step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw10088step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw10088step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10088 raw10088Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw10088 raw10088Labels = mixedMoment B raw10088step0 raw10088step0Labels := by
      have hz : ∀ j, raw10088 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10088step0 = (fun i j => raw10088 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10088step0 raw10088; decide +kernel
      have hl : raw10088step0Labels = raw10088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10088 raw10088Labels permutation346 hz
    mixedMoment B raw10088step0 raw10088step0Labels = mixedMoment B raw10088step1 raw10088step1Labels := by
      have ha : raw10088step1 = (fun i j => raw10088step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw10088step1 raw10088step0; decide +kernel
      have hl : raw10088step1Labels = raw10088step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10088step0 raw10088step0Labels permutation137 permutation5
    mixedMoment B raw10088step1 raw10088step1Labels = mixedMoment B raw10088step2 raw10088step2Labels := by
      have ha : raw10088step2 = raw10088step1 := by apply Matrix.ext; unfold raw10088step2 raw10088step1; decide +kernel
      have hl : raw10088step1Labels = labelEmbedding8 ∘ raw10088step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10088step1 raw10088step1Labels raw10088step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw10089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw10089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10089 raw10089Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw10089 raw10089Labels = mixedMoment B raw10089step0 raw10089step0Labels := by
      have hz : ∀ j, raw10089 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10089step0 = (fun i j => raw10089 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10089step0 raw10089; decide +kernel
      have hl : raw10089step0Labels = raw10089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10089 raw10089Labels permutation346 hz
    mixedMoment B raw10089step0 raw10089step0Labels = mixedMoment B raw10089step1 raw10089step1Labels := by
      have ha : raw10089step1 = (fun i j => raw10089step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw10089step1 raw10089step0; decide +kernel
      have hl : raw10089step1Labels = raw10089step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10089step0 raw10089step0Labels permutation33 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw10090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw10090step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10090step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw10090step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10090 raw10090Labels = mixedMoment B node4419 node4419Labels := by
  calc
    mixedMoment B raw10090 raw10090Labels = mixedMoment B raw10090step0 raw10090step0Labels := by
      have hz : ∀ j, raw10090 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10090step0 = (fun i j => raw10090 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10090step0 raw10090; decide +kernel
      have hl : raw10090step0Labels = raw10090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10090 raw10090Labels permutation346 hz
    mixedMoment B raw10090step0 raw10090step0Labels = mixedMoment B raw10090step1 raw10090step1Labels := by
      have ha : raw10090step1 = (fun i j => raw10090step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10090step1 raw10090step0; decide +kernel
      have hl : raw10090step1Labels = raw10090step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10090step0 raw10090step0Labels permutation40 permutation3
    mixedMoment B raw10090step1 raw10090step1Labels = mixedMoment B raw10090step2 raw10090step2Labels := by
      have ha : raw10090step2 = raw10090step1 := by apply Matrix.ext; unfold raw10090step2 raw10090step1; decide +kernel
      have hl : raw10090step1Labels = labelEmbedding6 ∘ raw10090step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10090step1 raw10090step1Labels raw10090step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4419 node4419Labels := by rfl

def raw10091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw10091step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw10091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10091 raw10091Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw10091 raw10091Labels = mixedMoment B raw10091step0 raw10091step0Labels := by
      have ha : raw10091step0 = (fun i j => raw10091 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10091step0 raw10091; decide +kernel
      have hl : raw10091step0Labels = raw10091Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10091 raw10091Labels permutation184 permutation3
    mixedMoment B raw10091step0 raw10091step0Labels = mixedMoment B raw10091step1 raw10091step1Labels := by
      have ha : raw10091step1 = raw10091step0 := by apply Matrix.ext; unfold raw10091step1 raw10091step0; decide +kernel
      have hl : raw10091step0Labels = labelEmbedding6 ∘ raw10091step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10091step0 raw10091step0Labels raw10091step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

def raw10092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw10092step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10092step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw10092step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10092 raw10092Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw10092 raw10092Labels = mixedMoment B raw10092step0 raw10092step0Labels := by
      have hz : ∀ j, raw10092 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10092step0 = (fun i j => raw10092 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10092step0 raw10092; decide +kernel
      have hl : raw10092step0Labels = raw10092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10092 raw10092Labels permutation346 hz
    mixedMoment B raw10092step0 raw10092step0Labels = mixedMoment B raw10092step1 raw10092step1Labels := by
      have ha : raw10092step1 = (fun i j => raw10092step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10092step1 raw10092step0; decide +kernel
      have hl : raw10092step1Labels = raw10092step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10092step0 raw10092step0Labels permutation40 permutation3
    mixedMoment B raw10092step1 raw10092step1Labels = mixedMoment B raw10092step2 raw10092step2Labels := by
      have ha : raw10092step2 = raw10092step1 := by apply Matrix.ext; unfold raw10092step2 raw10092step1; decide +kernel
      have hl : raw10092step1Labels = labelEmbedding6 ∘ raw10092step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10092step1 raw10092step1Labels raw10092step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

def raw10093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10093step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10093step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw10093step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10093 raw10093Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw10093 raw10093Labels = mixedMoment B raw10093step0 raw10093step0Labels := by
      have hz : ∀ j, raw10093 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10093step0 = (fun i j => raw10093 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10093step0 raw10093; decide +kernel
      have hl : raw10093step0Labels = raw10093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10093 raw10093Labels permutation346 hz
    mixedMoment B raw10093step0 raw10093step0Labels = mixedMoment B raw10093step1 raw10093step1Labels := by
      have ha : raw10093step1 = (fun i j => raw10093step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10093step1 raw10093step0; decide +kernel
      have hl : raw10093step1Labels = raw10093step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10093step0 raw10093step0Labels permutation40 permutation3
    mixedMoment B raw10093step1 raw10093step1Labels = mixedMoment B raw10093step2 raw10093step2Labels := by
      have ha : raw10093step2 = raw10093step1 := by apply Matrix.ext; unfold raw10093step2 raw10093step1; decide +kernel
      have hl : raw10093step1Labels = labelEmbedding6 ∘ raw10093step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10093step1 raw10093step1Labels raw10093step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

def raw10094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10094step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10094step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10094step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw10094step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10094 raw10094Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw10094 raw10094Labels = mixedMoment B raw10094step0 raw10094step0Labels := by
      have hz : ∀ j, raw10094 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10094step0 = (fun i j => raw10094 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10094step0 raw10094; decide +kernel
      have hl : raw10094step0Labels = raw10094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10094 raw10094Labels permutation346 hz
    mixedMoment B raw10094step0 raw10094step0Labels = mixedMoment B raw10094step1 raw10094step1Labels := by
      have ha : raw10094step1 = (fun i j => raw10094step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10094step1 raw10094step0; decide +kernel
      have hl : raw10094step1Labels = raw10094step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10094step0 raw10094step0Labels permutation41 permutation3
    mixedMoment B raw10094step1 raw10094step1Labels = mixedMoment B raw10094step2 raw10094step2Labels := by
      have ha : raw10094step2 = raw10094step1 := by apply Matrix.ext; unfold raw10094step2 raw10094step1; decide +kernel
      have hl : raw10094step1Labels = labelEmbedding6 ∘ raw10094step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10094step1 raw10094step1Labels raw10094step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw10095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10095step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10095step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10095 raw10095Labels = mixedMoment B node4396 node4396Labels := by
  calc
    mixedMoment B raw10095 raw10095Labels = mixedMoment B raw10095step0 raw10095step0Labels := by
      have ha : raw10095step0 = (fun i j => raw10095 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10095step0 raw10095; decide +kernel
      have hl : raw10095step0Labels = raw10095Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10095 raw10095Labels permutation202 permutation3
    mixedMoment B raw10095step0 raw10095step0Labels = mixedMoment B raw10095step1 raw10095step1Labels := by
      have ha : raw10095step1 = raw10095step0 := by apply Matrix.ext; unfold raw10095step1 raw10095step0; decide +kernel
      have hl : raw10095step0Labels = labelEmbedding6 ∘ raw10095step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10095step0 raw10095step0Labels raw10095step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4396 node4396Labels := by rfl

def raw10096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10096step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10096step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10096step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10096 raw10096Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw10096 raw10096Labels = mixedMoment B raw10096step0 raw10096step0Labels := by
      have ha : raw10096step0 = (fun i j => raw10096 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10096step0 raw10096; decide +kernel
      have hl : raw10096step0Labels = raw10096Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10096 raw10096Labels permutation160 permutation3
    mixedMoment B raw10096step0 raw10096step0Labels = mixedMoment B raw10096step1 raw10096step1Labels := by
      have ha : raw10096step1 = raw10096step0 := by apply Matrix.ext; unfold raw10096step1 raw10096step0; decide +kernel
      have hl : raw10096step0Labels = labelEmbedding6 ∘ raw10096step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10096step0 raw10096step0Labels raw10096step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw10097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10097step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw10097step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10097 raw10097Labels = mixedMoment B node4996 node4996Labels := by
  calc
    mixedMoment B raw10097 raw10097Labels = mixedMoment B raw10097step0 raw10097step0Labels := by
      have ha : raw10097step0 = (fun i j => raw10097 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10097step0 raw10097; decide +kernel
      have hl : raw10097step0Labels = raw10097Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10097 raw10097Labels permutation202 permutation3
    mixedMoment B raw10097step0 raw10097step0Labels = mixedMoment B raw10097step1 raw10097step1Labels := by
      have ha : raw10097step1 = raw10097step0 := by apply Matrix.ext; unfold raw10097step1 raw10097step0; decide +kernel
      have hl : raw10097step0Labels = labelEmbedding6 ∘ raw10097step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10097step0 raw10097step0Labels raw10097step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4996 node4996Labels := by rfl

def raw10098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10098step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10098step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw10098step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10098 raw10098Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw10098 raw10098Labels = mixedMoment B raw10098step0 raw10098step0Labels := by
      have ha : raw10098step0 = (fun i j => raw10098 (permutation212 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10098step0 raw10098; decide +kernel
      have hl : raw10098step0Labels = raw10098Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10098 raw10098Labels permutation212 permutation3
    mixedMoment B raw10098step0 raw10098step0Labels = mixedMoment B raw10098step1 raw10098step1Labels := by
      have ha : raw10098step1 = raw10098step0 := by apply Matrix.ext; unfold raw10098step1 raw10098step0; decide +kernel
      have hl : raw10098step0Labels = labelEmbedding6 ∘ raw10098step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10098step0 raw10098step0Labels raw10098step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

def raw10099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10099step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10099step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw10099step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10099 raw10099Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw10099 raw10099Labels = mixedMoment B raw10099step0 raw10099step0Labels := by
      have ha : raw10099step0 = (fun i j => raw10099 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10099step0 raw10099; decide +kernel
      have hl : raw10099step0Labels = raw10099Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10099 raw10099Labels permutation202 permutation3
    mixedMoment B raw10099step0 raw10099step0Labels = mixedMoment B raw10099step1 raw10099step1Labels := by
      have ha : raw10099step1 = raw10099step0 := by apply Matrix.ext; unfold raw10099step1 raw10099step0; decide +kernel
      have hl : raw10099step0Labels = labelEmbedding6 ∘ raw10099step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10099step0 raw10099step0Labels raw10099step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw10100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10100step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10100step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10100step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10100step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10100 raw10100Labels = mixedMoment B node4457 node4457Labels := by
  calc
    mixedMoment B raw10100 raw10100Labels = mixedMoment B raw10100step0 raw10100step0Labels := by
      have hz : ∀ j, raw10100 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10100step0 = (fun i j => raw10100 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10100step0 raw10100; decide +kernel
      have hl : raw10100step0Labels = raw10100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10100 raw10100Labels permutation346 hz
    mixedMoment B raw10100step0 raw10100step0Labels = mixedMoment B raw10100step1 raw10100step1Labels := by
      have ha : raw10100step1 = (fun i j => raw10100step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10100step1 raw10100step0; decide +kernel
      have hl : raw10100step1Labels = raw10100step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10100step0 raw10100step0Labels permutation32 permutation3
    mixedMoment B raw10100step1 raw10100step1Labels = mixedMoment B raw10100step2 raw10100step2Labels := by
      have ha : raw10100step2 = raw10100step1 := by apply Matrix.ext; unfold raw10100step2 raw10100step1; decide +kernel
      have hl : raw10100step1Labels = labelEmbedding6 ∘ raw10100step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10100step1 raw10100step1Labels raw10100step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4457 node4457Labels := by rfl

def raw10101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10101step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10101step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10101step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10101step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10101 raw10101Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw10101 raw10101Labels = mixedMoment B raw10101step0 raw10101step0Labels := by
      have hz : ∀ j, raw10101 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10101step0 = (fun i j => raw10101 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10101step0 raw10101; decide +kernel
      have hl : raw10101step0Labels = raw10101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10101 raw10101Labels permutation346 hz
    mixedMoment B raw10101step0 raw10101step0Labels = mixedMoment B raw10101step1 raw10101step1Labels := by
      have ha : raw10101step1 = (fun i j => raw10101step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10101step1 raw10101step0; decide +kernel
      have hl : raw10101step1Labels = raw10101step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10101step0 raw10101step0Labels permutation32 permutation3
    mixedMoment B raw10101step1 raw10101step1Labels = mixedMoment B raw10101step2 raw10101step2Labels := by
      have ha : raw10101step2 = raw10101step1 := by apply Matrix.ext; unfold raw10101step2 raw10101step1; decide +kernel
      have hl : raw10101step1Labels = labelEmbedding6 ∘ raw10101step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10101step1 raw10101step1Labels raw10101step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5168 node5168Labels := by rfl

def raw10102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw10102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10102step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10102step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw10102step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10102 raw10102Labels = mixedMoment B node5072 node5072Labels := by
  calc
    mixedMoment B raw10102 raw10102Labels = mixedMoment B raw10102step0 raw10102step0Labels := by
      have ha : raw10102step0 = (fun i j => raw10102 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10102step0 raw10102; decide +kernel
      have hl : raw10102step0Labels = raw10102Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10102 raw10102Labels permutation176 permutation3
    mixedMoment B raw10102step0 raw10102step0Labels = mixedMoment B raw10102step1 raw10102step1Labels := by
      have ha : raw10102step1 = raw10102step0 := by apply Matrix.ext; unfold raw10102step1 raw10102step0; decide +kernel
      have hl : raw10102step0Labels = labelEmbedding6 ∘ raw10102step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10102step0 raw10102step0Labels raw10102step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5072 node5072Labels := by rfl

def raw10103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw10103step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10103step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw10103step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10103 raw10103Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw10103 raw10103Labels = mixedMoment B raw10103step0 raw10103step0Labels := by
      have hz : ∀ j, raw10103 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10103step0 = (fun i j => raw10103 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10103step0 raw10103; decide +kernel
      have hl : raw10103step0Labels = raw10103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10103 raw10103Labels permutation346 hz
    mixedMoment B raw10103step0 raw10103step0Labels = mixedMoment B raw10103step1 raw10103step1Labels := by
      have ha : raw10103step1 = (fun i j => raw10103step0 (permutation44 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10103step1 raw10103step0; decide +kernel
      have hl : raw10103step1Labels = raw10103step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10103step0 raw10103step0Labels permutation44 permutation3
    mixedMoment B raw10103step1 raw10103step1Labels = mixedMoment B raw10103step2 raw10103step2Labels := by
      have ha : raw10103step2 = raw10103step1 := by apply Matrix.ext; unfold raw10103step2 raw10103step1; decide +kernel
      have hl : raw10103step1Labels = labelEmbedding6 ∘ raw10103step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10103step1 raw10103step1Labels raw10103step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw10104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw10104step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10104step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10104step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10104step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw10104step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10104 raw10104Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw10104 raw10104Labels = mixedMoment B raw10104step0 raw10104step0Labels := by
      have hz : ∀ j, raw10104 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10104step0 = (fun i j => raw10104 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10104step0 raw10104; decide +kernel
      have hl : raw10104step0Labels = raw10104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10104 raw10104Labels permutation346 hz
    mixedMoment B raw10104step0 raw10104step0Labels = mixedMoment B raw10104step1 raw10104step1Labels := by
      have ha : raw10104step1 = (fun i j => raw10104step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10104step1 raw10104step0; decide +kernel
      have hl : raw10104step1Labels = raw10104step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10104step0 raw10104step0Labels permutation32 permutation3
    mixedMoment B raw10104step1 raw10104step1Labels = mixedMoment B raw10104step2 raw10104step2Labels := by
      have ha : raw10104step2 = raw10104step1 := by apply Matrix.ext; unfold raw10104step2 raw10104step1; decide +kernel
      have hl : raw10104step1Labels = labelEmbedding6 ∘ raw10104step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10104step1 raw10104step1Labels raw10104step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw10105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10105step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw10105step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10105step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw10105step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10105 raw10105Labels = mixedMoment B node4404 node4404Labels := by
  calc
    mixedMoment B raw10105 raw10105Labels = mixedMoment B raw10105step0 raw10105step0Labels := by
      have hz : ∀ j, raw10105 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10105step0 = (fun i j => raw10105 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10105step0 raw10105; decide +kernel
      have hl : raw10105step0Labels = raw10105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10105 raw10105Labels permutation346 hz
    mixedMoment B raw10105step0 raw10105step0Labels = mixedMoment B raw10105step1 raw10105step1Labels := by
      have ha : raw10105step1 = (fun i j => raw10105step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10105step1 raw10105step0; decide +kernel
      have hl : raw10105step1Labels = raw10105step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10105step0 raw10105step0Labels permutation38 permutation3
    mixedMoment B raw10105step1 raw10105step1Labels = mixedMoment B raw10105step2 raw10105step2Labels := by
      have ha : raw10105step2 = raw10105step1 := by apply Matrix.ext; unfold raw10105step2 raw10105step1; decide +kernel
      have hl : raw10105step1Labels = labelEmbedding6 ∘ raw10105step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10105step1 raw10105step1Labels raw10105step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4404 node4404Labels := by rfl

def raw10106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10106step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10106step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10106step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw10106step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10106 raw10106Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw10106 raw10106Labels = mixedMoment B raw10106step0 raw10106step0Labels := by
      have hz : ∀ j, raw10106 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10106step0 = (fun i j => raw10106 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10106step0 raw10106; decide +kernel
      have hl : raw10106step0Labels = raw10106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10106 raw10106Labels permutation346 hz
    mixedMoment B raw10106step0 raw10106step0Labels = mixedMoment B raw10106step1 raw10106step1Labels := by
      have ha : raw10106step1 = (fun i j => raw10106step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10106step1 raw10106step0; decide +kernel
      have hl : raw10106step1Labels = raw10106step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10106step0 raw10106step0Labels permutation32 permutation3
    mixedMoment B raw10106step1 raw10106step1Labels = mixedMoment B raw10106step2 raw10106step2Labels := by
      have ha : raw10106step2 = raw10106step1 := by apply Matrix.ext; unfold raw10106step2 raw10106step1; decide +kernel
      have hl : raw10106step1Labels = labelEmbedding6 ∘ raw10106step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10106step1 raw10106step1Labels raw10106step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw10107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw10107step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10107step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw10107step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10107 raw10107Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw10107 raw10107Labels = mixedMoment B raw10107step0 raw10107step0Labels := by
      have ha : raw10107step0 = (fun i j => raw10107 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10107step0 raw10107; decide +kernel
      have hl : raw10107step0Labels = raw10107Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10107 raw10107Labels permutation182 permutation3
    mixedMoment B raw10107step0 raw10107step0Labels = mixedMoment B raw10107step1 raw10107step1Labels := by
      have ha : raw10107step1 = raw10107step0 := by apply Matrix.ext; unfold raw10107step1 raw10107step0; decide +kernel
      have hl : raw10107step0Labels = labelEmbedding6 ∘ raw10107step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10107step0 raw10107step0Labels raw10107step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5050 node5050Labels := by rfl

def raw10108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw10108step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw10108step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw10108step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10108 raw10108Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw10108 raw10108Labels = mixedMoment B raw10108step0 raw10108step0Labels := by
      have hz : ∀ j, raw10108 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10108step0 = (fun i j => raw10108 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10108step0 raw10108; decide +kernel
      have hl : raw10108step0Labels = raw10108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10108 raw10108Labels permutation346 hz
    mixedMoment B raw10108step0 raw10108step0Labels = mixedMoment B raw10108step1 raw10108step1Labels := by
      have ha : raw10108step1 = (fun i j => raw10108step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10108step1 raw10108step0; decide +kernel
      have hl : raw10108step1Labels = raw10108step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10108step0 raw10108step0Labels permutation38 permutation3
    mixedMoment B raw10108step1 raw10108step1Labels = mixedMoment B raw10108step2 raw10108step2Labels := by
      have ha : raw10108step2 = raw10108step1 := by apply Matrix.ext; unfold raw10108step2 raw10108step1; decide +kernel
      have hl : raw10108step1Labels = labelEmbedding6 ∘ raw10108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10108step1 raw10108step1Labels raw10108step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5003 node5003Labels := by rfl

def raw10109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw10109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw10109step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10109step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10109step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10109step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw10109step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10109 raw10109Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw10109 raw10109Labels = mixedMoment B raw10109step0 raw10109step0Labels := by
      have hz : ∀ j, raw10109 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10109step0 = (fun i j => raw10109 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10109step0 raw10109; decide +kernel
      have hl : raw10109step0Labels = raw10109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10109 raw10109Labels permutation346 hz
    mixedMoment B raw10109step0 raw10109step0Labels = mixedMoment B raw10109step1 raw10109step1Labels := by
      have ha : raw10109step1 = (fun i j => raw10109step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10109step1 raw10109step0; decide +kernel
      have hl : raw10109step1Labels = raw10109step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10109step0 raw10109step0Labels permutation39 permutation3
    mixedMoment B raw10109step1 raw10109step1Labels = mixedMoment B raw10109step2 raw10109step2Labels := by
      have ha : raw10109step2 = raw10109step1 := by apply Matrix.ext; unfold raw10109step2 raw10109step1; decide +kernel
      have hl : raw10109step1Labels = labelEmbedding6 ∘ raw10109step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10109step1 raw10109step1Labels raw10109step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw10110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10110step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw10110step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10110step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw10110step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10110 raw10110Labels = mixedMoment B node4398 node4398Labels := by
  calc
    mixedMoment B raw10110 raw10110Labels = mixedMoment B raw10110step0 raw10110step0Labels := by
      have hz : ∀ j, raw10110 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10110step0 = (fun i j => raw10110 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10110step0 raw10110; decide +kernel
      have hl : raw10110step0Labels = raw10110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10110 raw10110Labels permutation346 hz
    mixedMoment B raw10110step0 raw10110step0Labels = mixedMoment B raw10110step1 raw10110step1Labels := by
      have ha : raw10110step1 = (fun i j => raw10110step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10110step1 raw10110step0; decide +kernel
      have hl : raw10110step1Labels = raw10110step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10110step0 raw10110step0Labels permutation38 permutation3
    mixedMoment B raw10110step1 raw10110step1Labels = mixedMoment B raw10110step2 raw10110step2Labels := by
      have ha : raw10110step2 = raw10110step1 := by apply Matrix.ext; unfold raw10110step2 raw10110step1; decide +kernel
      have hl : raw10110step1Labels = labelEmbedding6 ∘ raw10110step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10110step1 raw10110step1Labels raw10110step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4398 node4398Labels := by rfl

def raw10111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw10111step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw10111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw10111step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10111step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10111step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw10111step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw10111step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical10111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw10111 raw10111Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw10111 raw10111Labels = mixedMoment B raw10111step0 raw10111step0Labels := by
      have hz : ∀ j, raw10111 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw10111step0 = (fun i j => raw10111 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw10111step0 raw10111; decide +kernel
      have hl : raw10111step0Labels = raw10111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw10111 raw10111Labels permutation346 hz
    mixedMoment B raw10111step0 raw10111step0Labels = mixedMoment B raw10111step1 raw10111step1Labels := by
      have ha : raw10111step1 = (fun i j => raw10111step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw10111step1 raw10111step0; decide +kernel
      have hl : raw10111step1Labels = raw10111step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw10111step0 raw10111step0Labels permutation151 permutation3
    mixedMoment B raw10111step1 raw10111step1Labels = mixedMoment B raw10111step2 raw10111step2Labels := by
      have ha : raw10111step2 = -raw10111step1 := by apply Matrix.ext; change ∀ i j, raw10111step2 i j = -(raw10111step1 i j); unfold raw10111step2 raw10111step1; decide +kernel
      have hl : raw10111step2Labels = raw10111step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw10111step2 raw10111step2Labels = mixedMoment B raw10111step3 raw10111step3Labels := by
      have ha : raw10111step3 = raw10111step2 := by apply Matrix.ext; unfold raw10111step3 raw10111step2; decide +kernel
      have hl : raw10111step2Labels = labelEmbedding6 ∘ raw10111step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw10111step2 raw10111step2Labels raw10111step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
