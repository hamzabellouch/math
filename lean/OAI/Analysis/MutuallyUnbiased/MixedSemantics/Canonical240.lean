import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw30720 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30720Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30720step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30720step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30720step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30720step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30720 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30720 raw30720Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw30720 raw30720Labels = mixedMoment B raw30720step0 raw30720step0Labels := by
      have hz : ∀ j, raw30720 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30720step0 = (fun i j => raw30720 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30720step0 raw30720; decide +kernel
      have hl : raw30720step0Labels = raw30720Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30720 raw30720Labels permutation346 hz
    mixedMoment B raw30720step0 raw30720step0Labels = mixedMoment B raw30720step1 raw30720step1Labels := by
      have ha : raw30720step1 = (fun i j => raw30720step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30720step1 raw30720step0; decide +kernel
      have hl : raw30720step1Labels = raw30720step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30720step0 raw30720step0Labels permutation33 permutation2
    _ = mixedMoment B node5101 node5101Labels := by rfl

def raw30721 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30721Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30721step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30721step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30721step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30721step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30721step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw30721step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30721 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30721 raw30721Labels = mixedMoment B node4558 node4558Labels := by
  calc
    mixedMoment B raw30721 raw30721Labels = mixedMoment B raw30721step0 raw30721step0Labels := by
      have hz : ∀ j, raw30721 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30721step0 = (fun i j => raw30721 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30721step0 raw30721; decide +kernel
      have hl : raw30721step0Labels = raw30721Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30721 raw30721Labels permutation434 hz
    mixedMoment B raw30721step0 raw30721step0Labels = mixedMoment B raw30721step1 raw30721step1Labels := by
      have hz : ∀ j, raw30721step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30721step1 = (fun i j => raw30721step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30721step1 raw30721step0; decide +kernel
      have hl : raw30721step1Labels = raw30721step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30721step0 raw30721step0Labels permutation80 hz
    mixedMoment B raw30721step1 raw30721step1Labels = mixedMoment B raw30721step2 raw30721step2Labels := by
      have ha : raw30721step2 = (fun i j => raw30721step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30721step2 raw30721step1; decide +kernel
      have hl : raw30721step2Labels = raw30721step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30721step1 raw30721step1Labels permutation9 permutation2
    _ = mixedMoment B node4558 node4558Labels := by rfl

def raw30722 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30722Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30722step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30722step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30722step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30722step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30722step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -1, -1], ![3, -1, -2]]
def raw30722step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30722 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30722 raw30722Labels = mixedMoment B node4952 node4952Labels := by
  calc
    mixedMoment B raw30722 raw30722Labels = mixedMoment B raw30722step0 raw30722step0Labels := by
      have hz : ∀ j, raw30722 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30722step0 = (fun i j => raw30722 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30722step0 raw30722; decide +kernel
      have hl : raw30722step0Labels = raw30722Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30722 raw30722Labels permutation434 hz
    mixedMoment B raw30722step0 raw30722step0Labels = mixedMoment B raw30722step1 raw30722step1Labels := by
      have hz : ∀ j, raw30722step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30722step1 = (fun i j => raw30722step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30722step1 raw30722step0; decide +kernel
      have hl : raw30722step1Labels = raw30722step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30722step0 raw30722step0Labels permutation80 hz
    mixedMoment B raw30722step1 raw30722step1Labels = mixedMoment B raw30722step2 raw30722step2Labels := by
      have ha : raw30722step2 = (fun i j => raw30722step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30722step2 raw30722step1; decide +kernel
      have hl : raw30722step2Labels = raw30722step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30722step1 raw30722step1Labels permutation9 permutation2
    _ = mixedMoment B node4952 node4952Labels := by rfl

def raw30723 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30723Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30723step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30723step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30723step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30723step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30723step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30723step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30723 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30723 raw30723Labels = mixedMoment B node4943 node4943Labels := by
  calc
    mixedMoment B raw30723 raw30723Labels = mixedMoment B raw30723step0 raw30723step0Labels := by
      have hz : ∀ j, raw30723 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30723step0 = (fun i j => raw30723 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30723step0 raw30723; decide +kernel
      have hl : raw30723step0Labels = raw30723Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30723 raw30723Labels permutation434 hz
    mixedMoment B raw30723step0 raw30723step0Labels = mixedMoment B raw30723step1 raw30723step1Labels := by
      have ha : raw30723step1 = (fun i j => raw30723step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30723step1 raw30723step0; decide +kernel
      have hl : raw30723step1Labels = raw30723step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30723step0 raw30723step0Labels permutation127 permutation2
    mixedMoment B raw30723step1 raw30723step1Labels = mixedMoment B raw30723step2 raw30723step2Labels := by
      have ha : raw30723step2 = -raw30723step1 := by apply Matrix.ext; change ∀ i j, raw30723step2 i j = -(raw30723step1 i j); unfold raw30723step2 raw30723step1; decide +kernel
      have hl : raw30723step2Labels = raw30723step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4943 node4943Labels := by rfl

def raw30724 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30724Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30724step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30724step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30724step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30724step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30724step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30724step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30724 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30724 raw30724Labels = mixedMoment B node4943 node4943Labels := by
  calc
    mixedMoment B raw30724 raw30724Labels = mixedMoment B raw30724step0 raw30724step0Labels := by
      have hz : ∀ j, raw30724 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30724step0 = (fun i j => raw30724 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30724step0 raw30724; decide +kernel
      have hl : raw30724step0Labels = raw30724Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30724 raw30724Labels permutation346 hz
    mixedMoment B raw30724step0 raw30724step0Labels = mixedMoment B raw30724step1 raw30724step1Labels := by
      have ha : raw30724step1 = (fun i j => raw30724step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30724step1 raw30724step0; decide +kernel
      have hl : raw30724step1Labels = raw30724step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30724step0 raw30724step0Labels permutation127 permutation2
    mixedMoment B raw30724step1 raw30724step1Labels = mixedMoment B raw30724step2 raw30724step2Labels := by
      have ha : raw30724step2 = -raw30724step1 := by apply Matrix.ext; change ∀ i j, raw30724step2 i j = -(raw30724step1 i j); unfold raw30724step2 raw30724step1; decide +kernel
      have hl : raw30724step2Labels = raw30724step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4943 node4943Labels := by rfl

def raw30725 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw30725Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30725step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw30725step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30725step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![3, -1, -2], ![1, 0, -1]]
def raw30725step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30725step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw30725step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30725 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30725 raw30725Labels = mixedMoment B node5107 node5107Labels := by
  calc
    mixedMoment B raw30725 raw30725Labels = mixedMoment B raw30725step0 raw30725step0Labels := by
      have hz : ∀ j, raw30725 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30725step0 = (fun i j => raw30725 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30725step0 raw30725; decide +kernel
      have hl : raw30725step0Labels = raw30725Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30725 raw30725Labels permutation434 hz
    mixedMoment B raw30725step0 raw30725step0Labels = mixedMoment B raw30725step1 raw30725step1Labels := by
      have hz : ∀ j, raw30725step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30725step1 = (fun i j => raw30725step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30725step1 raw30725step0; decide +kernel
      have hl : raw30725step1Labels = raw30725step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30725step0 raw30725step0Labels permutation80 hz
    mixedMoment B raw30725step1 raw30725step1Labels = mixedMoment B raw30725step2 raw30725step2Labels := by
      have ha : raw30725step2 = (fun i j => raw30725step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30725step2 raw30725step1; decide +kernel
      have hl : raw30725step2Labels = raw30725step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30725step1 raw30725step1Labels permutation9 permutation2
    _ = mixedMoment B node5107 node5107Labels := by rfl

def raw30726 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30726Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30726step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30726step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30726step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30726step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30726 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30726 raw30726Labels = mixedMoment B node4559 node4559Labels := by
  calc
    mixedMoment B raw30726 raw30726Labels = mixedMoment B raw30726step0 raw30726step0Labels := by
      have hz : ∀ j, raw30726 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30726step0 = (fun i j => raw30726 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30726step0 raw30726; decide +kernel
      have hl : raw30726step0Labels = raw30726Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30726 raw30726Labels permutation434 hz
    mixedMoment B raw30726step0 raw30726step0Labels = mixedMoment B raw30726step1 raw30726step1Labels := by
      have hz : ∀ j, raw30726step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30726step1 = (fun i j => raw30726step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30726step1 raw30726step0; decide +kernel
      have hl : raw30726step1Labels = raw30726step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30726step0 raw30726step0Labels permutation80 hz
    _ = mixedMoment B node4559 node4559Labels := by rfl

def raw30727 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30727Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30727step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30727step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30727step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30727step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30727 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30727 raw30727Labels = mixedMoment B node4953 node4953Labels := by
  calc
    mixedMoment B raw30727 raw30727Labels = mixedMoment B raw30727step0 raw30727step0Labels := by
      have hz : ∀ j, raw30727 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30727step0 = (fun i j => raw30727 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30727step0 raw30727; decide +kernel
      have hl : raw30727step0Labels = raw30727Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30727 raw30727Labels permutation434 hz
    mixedMoment B raw30727step0 raw30727step0Labels = mixedMoment B raw30727step1 raw30727step1Labels := by
      have hz : ∀ j, raw30727step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30727step1 = (fun i j => raw30727step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30727step1 raw30727step0; decide +kernel
      have hl : raw30727step1Labels = raw30727step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30727step0 raw30727step0Labels permutation80 hz
    _ = mixedMoment B node4953 node4953Labels := by rfl

def raw30728 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30728Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30728step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30728step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30728step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30728step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30728step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30728step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30728step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30728step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30728 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30728 raw30728Labels = mixedMoment B node4972 node4972Labels := by
  calc
    mixedMoment B raw30728 raw30728Labels = mixedMoment B raw30728step0 raw30728step0Labels := by
      have hz : ∀ j, raw30728 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30728step0 = (fun i j => raw30728 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30728step0 raw30728; decide +kernel
      have hl : raw30728step0Labels = raw30728Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30728 raw30728Labels permutation434 hz
    mixedMoment B raw30728step0 raw30728step0Labels = mixedMoment B raw30728step1 raw30728step1Labels := by
      have ha : raw30728step1 = (fun i j => raw30728step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30728step1 raw30728step0; decide +kernel
      have hl : raw30728step1Labels = raw30728step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30728step0 raw30728step0Labels permutation149 permutation3
    mixedMoment B raw30728step1 raw30728step1Labels = mixedMoment B raw30728step2 raw30728step2Labels := by
      have ha : raw30728step2 = -raw30728step1 := by apply Matrix.ext; change ∀ i j, raw30728step2 i j = -(raw30728step1 i j); unfold raw30728step2 raw30728step1; decide +kernel
      have hl : raw30728step2Labels = raw30728step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30728step2 raw30728step2Labels = mixedMoment B raw30728step3 raw30728step3Labels := by
      have ha : raw30728step3 = raw30728step2 := by apply Matrix.ext; unfold raw30728step3 raw30728step2; decide +kernel
      have hl : raw30728step2Labels = labelEmbedding6 ∘ raw30728step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30728step2 raw30728step2Labels raw30728step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4972 node4972Labels := by rfl

def raw30729 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30729Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30729step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30729step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30729step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30729step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30729step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30729step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30729step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30729step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30729 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30729 raw30729Labels = mixedMoment B node4972 node4972Labels := by
  calc
    mixedMoment B raw30729 raw30729Labels = mixedMoment B raw30729step0 raw30729step0Labels := by
      have hz : ∀ j, raw30729 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30729step0 = (fun i j => raw30729 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30729step0 raw30729; decide +kernel
      have hl : raw30729step0Labels = raw30729Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30729 raw30729Labels permutation346 hz
    mixedMoment B raw30729step0 raw30729step0Labels = mixedMoment B raw30729step1 raw30729step1Labels := by
      have ha : raw30729step1 = (fun i j => raw30729step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30729step1 raw30729step0; decide +kernel
      have hl : raw30729step1Labels = raw30729step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30729step0 raw30729step0Labels permutation149 permutation3
    mixedMoment B raw30729step1 raw30729step1Labels = mixedMoment B raw30729step2 raw30729step2Labels := by
      have ha : raw30729step2 = -raw30729step1 := by apply Matrix.ext; change ∀ i j, raw30729step2 i j = -(raw30729step1 i j); unfold raw30729step2 raw30729step1; decide +kernel
      have hl : raw30729step2Labels = raw30729step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30729step2 raw30729step2Labels = mixedMoment B raw30729step3 raw30729step3Labels := by
      have ha : raw30729step3 = raw30729step2 := by apply Matrix.ext; unfold raw30729step3 raw30729step2; decide +kernel
      have hl : raw30729step2Labels = labelEmbedding6 ∘ raw30729step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30729step2 raw30729step2Labels raw30729step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4972 node4972Labels := by rfl

def raw30730 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30730Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30730step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30730step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30730step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30730step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30730step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30730step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30730step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 1, -2], ![2, 0, -2]]
def raw30730step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30730 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30730 raw30730Labels = mixedMoment B node3775 node3775Labels := by
  calc
    mixedMoment B raw30730 raw30730Labels = mixedMoment B raw30730step0 raw30730step0Labels := by
      have hz : ∀ j, raw30730 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30730step0 = (fun i j => raw30730 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30730step0 raw30730; decide +kernel
      have hl : raw30730step0Labels = raw30730Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30730 raw30730Labels permutation434 hz
    mixedMoment B raw30730step0 raw30730step0Labels = mixedMoment B raw30730step1 raw30730step1Labels := by
      have hz : ∀ j, raw30730step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30730step1 = (fun i j => raw30730step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30730step1 raw30730step0; decide +kernel
      have hl : raw30730step1Labels = raw30730step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30730step0 raw30730step0Labels permutation80 hz
    mixedMoment B raw30730step1 raw30730step1Labels = mixedMoment B raw30730step2 raw30730step2Labels := by
      have ha : raw30730step2 = (fun i j => raw30730step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30730step2 raw30730step1; decide +kernel
      have hl : raw30730step2Labels = raw30730step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30730step1 raw30730step1Labels permutation25 permutation7
    mixedMoment B raw30730step2 raw30730step2Labels = mixedMoment B raw30730step3 raw30730step3Labels := by
      have ha : raw30730step3 = raw30730step2 := by apply Matrix.ext; unfold raw30730step3 raw30730step2; decide +kernel
      have hl : raw30730step2Labels = labelEmbedding1 ∘ raw30730step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30730step2 raw30730step2Labels raw30730step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3775 node3775Labels := by rfl

def raw30731 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30731Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30731step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30731step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30731step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30731step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30731step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30731step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30731 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30731 raw30731Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw30731 raw30731Labels = mixedMoment B raw30731step0 raw30731step0Labels := by
      have hz : ∀ j, raw30731 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30731step0 = (fun i j => raw30731 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30731step0 raw30731; decide +kernel
      have hl : raw30731step0Labels = raw30731Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30731 raw30731Labels permutation434 hz
    mixedMoment B raw30731step0 raw30731step0Labels = mixedMoment B raw30731step1 raw30731step1Labels := by
      have ha : raw30731step1 = (fun i j => raw30731step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30731step1 raw30731step0; decide +kernel
      have hl : raw30731step1Labels = raw30731step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30731step0 raw30731step0Labels permutation127 permutation7
    mixedMoment B raw30731step1 raw30731step1Labels = mixedMoment B raw30731step2 raw30731step2Labels := by
      have ha : raw30731step2 = raw30731step1 := by apply Matrix.ext; unfold raw30731step2 raw30731step1; decide +kernel
      have hl : raw30731step1Labels = labelEmbedding1 ∘ raw30731step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30731step1 raw30731step1Labels raw30731step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

def raw30732 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30732Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30732step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30732step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30732step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30732step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30732step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30732step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30732 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30732 raw30732Labels = mixedMoment B node3766 node3766Labels := by
  calc
    mixedMoment B raw30732 raw30732Labels = mixedMoment B raw30732step0 raw30732step0Labels := by
      have hz : ∀ j, raw30732 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30732step0 = (fun i j => raw30732 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30732step0 raw30732; decide +kernel
      have hl : raw30732step0Labels = raw30732Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30732 raw30732Labels permutation346 hz
    mixedMoment B raw30732step0 raw30732step0Labels = mixedMoment B raw30732step1 raw30732step1Labels := by
      have ha : raw30732step1 = (fun i j => raw30732step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30732step1 raw30732step0; decide +kernel
      have hl : raw30732step1Labels = raw30732step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30732step0 raw30732step0Labels permutation127 permutation7
    mixedMoment B raw30732step1 raw30732step1Labels = mixedMoment B raw30732step2 raw30732step2Labels := by
      have ha : raw30732step2 = raw30732step1 := by apply Matrix.ext; unfold raw30732step2 raw30732step1; decide +kernel
      have hl : raw30732step1Labels = labelEmbedding1 ∘ raw30732step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30732step1 raw30732step1Labels raw30732step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3766 node3766Labels := by rfl

def raw30733 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30733Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30733step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30733step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30733step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw30733step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30733step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw30733step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30733step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw30733step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30733step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw30733step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30733 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30733 raw30733Labels = mixedMoment B node3817 node3817Labels := by
  calc
    mixedMoment B raw30733 raw30733Labels = mixedMoment B raw30733step0 raw30733step0Labels := by
      have hz : ∀ j, raw30733 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30733step0 = (fun i j => raw30733 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30733step0 raw30733; decide +kernel
      have hl : raw30733step0Labels = raw30733Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30733 raw30733Labels permutation434 hz
    mixedMoment B raw30733step0 raw30733step0Labels = mixedMoment B raw30733step1 raw30733step1Labels := by
      have hz : ∀ j, raw30733step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30733step1 = (fun i j => raw30733step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30733step1 raw30733step0; decide +kernel
      have hl : raw30733step1Labels = raw30733step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30733step0 raw30733step0Labels permutation80 hz
    mixedMoment B raw30733step1 raw30733step1Labels = mixedMoment B raw30733step2 raw30733step2Labels := by
      have ha : raw30733step2 = (fun i j => raw30733step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30733step2 raw30733step1; decide +kernel
      have hl : raw30733step2Labels = raw30733step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30733step1 raw30733step1Labels permutation9 permutation7
    mixedMoment B raw30733step2 raw30733step2Labels = mixedMoment B raw30733step3 raw30733step3Labels := by
      have ha : raw30733step3 = -raw30733step2 := by apply Matrix.ext; change ∀ i j, raw30733step3 i j = -(raw30733step2 i j); unfold raw30733step3 raw30733step2; decide +kernel
      have hl : raw30733step3Labels = raw30733step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30733step3 raw30733step3Labels = mixedMoment B raw30733step4 raw30733step4Labels := by
      have ha : raw30733step4 = raw30733step3 := by apply Matrix.ext; unfold raw30733step4 raw30733step3; decide +kernel
      have hl : raw30733step3Labels = labelEmbedding1 ∘ raw30733step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30733step3 raw30733step3Labels raw30733step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3817 node3817Labels := by rfl

def raw30734 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30734Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30734step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30734step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30734step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30734step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30734step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw30734step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30734step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw30734step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical30734 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30734 raw30734Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw30734 raw30734Labels = mixedMoment B raw30734step0 raw30734step0Labels := by
      have hz : ∀ j, raw30734 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30734step0 = (fun i j => raw30734 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30734step0 raw30734; decide +kernel
      have hl : raw30734step0Labels = raw30734Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30734 raw30734Labels permutation434 hz
    mixedMoment B raw30734step0 raw30734step0Labels = mixedMoment B raw30734step1 raw30734step1Labels := by
      have hz : ∀ j, raw30734step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30734step1 = (fun i j => raw30734step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30734step1 raw30734step0; decide +kernel
      have hl : raw30734step1Labels = raw30734step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30734step0 raw30734step0Labels permutation80 hz
    mixedMoment B raw30734step1 raw30734step1Labels = mixedMoment B raw30734step2 raw30734step2Labels := by
      have hz : ∀ i, raw30734step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw30734step2 = (fun i j => raw30734step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw30734step2 raw30734step1; decide +kernel
      have hl : raw30734step2Labels = (fun j => raw30734step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw30734step1 raw30734step1Labels permutation4 hz
    mixedMoment B raw30734step2 raw30734step2Labels = mixedMoment B raw30734step3 raw30734step3Labels := by
      have ha : raw30734step3 = (fun i j => raw30734step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw30734step3 raw30734step2; decide +kernel
      have hl : raw30734step3Labels = raw30734step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30734step2 raw30734step2Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw30735 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30735Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30735step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30735step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30735step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw30735step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30735step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30735step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30735step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30735step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30735step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30735step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30735 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30735 raw30735Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw30735 raw30735Labels = mixedMoment B raw30735step0 raw30735step0Labels := by
      have hz : ∀ j, raw30735 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30735step0 = (fun i j => raw30735 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30735step0 raw30735; decide +kernel
      have hl : raw30735step0Labels = raw30735Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30735 raw30735Labels permutation434 hz
    mixedMoment B raw30735step0 raw30735step0Labels = mixedMoment B raw30735step1 raw30735step1Labels := by
      have hz : ∀ j, raw30735step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30735step1 = (fun i j => raw30735step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30735step1 raw30735step0; decide +kernel
      have hl : raw30735step1Labels = raw30735step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30735step0 raw30735step0Labels permutation80 hz
    mixedMoment B raw30735step1 raw30735step1Labels = mixedMoment B raw30735step2 raw30735step2Labels := by
      have ha : raw30735step2 = (fun i j => raw30735step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30735step2 raw30735step1; decide +kernel
      have hl : raw30735step2Labels = raw30735step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30735step1 raw30735step1Labels permutation9 permutation7
    mixedMoment B raw30735step2 raw30735step2Labels = mixedMoment B raw30735step3 raw30735step3Labels := by
      have ha : raw30735step3 = -raw30735step2 := by apply Matrix.ext; change ∀ i j, raw30735step3 i j = -(raw30735step2 i j); unfold raw30735step3 raw30735step2; decide +kernel
      have hl : raw30735step3Labels = raw30735step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30735step3 raw30735step3Labels = mixedMoment B raw30735step4 raw30735step4Labels := by
      have ha : raw30735step4 = raw30735step3 := by apply Matrix.ext; unfold raw30735step4 raw30735step3; decide +kernel
      have hl : raw30735step3Labels = labelEmbedding1 ∘ raw30735step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30735step3 raw30735step3Labels raw30735step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3301 node3301Labels := by rfl

def raw30736 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30736Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30736step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30736step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30736step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30736step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30736step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30736step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30736step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30736step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30736 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30736 raw30736Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw30736 raw30736Labels = mixedMoment B raw30736step0 raw30736step0Labels := by
      have hz : ∀ j, raw30736 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30736step0 = (fun i j => raw30736 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30736step0 raw30736; decide +kernel
      have hl : raw30736step0Labels = raw30736Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30736 raw30736Labels permutation434 hz
    mixedMoment B raw30736step0 raw30736step0Labels = mixedMoment B raw30736step1 raw30736step1Labels := by
      have ha : raw30736step1 = (fun i j => raw30736step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30736step1 raw30736step0; decide +kernel
      have hl : raw30736step1Labels = raw30736step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30736step0 raw30736step0Labels permutation33 permutation7
    mixedMoment B raw30736step1 raw30736step1Labels = mixedMoment B raw30736step2 raw30736step2Labels := by
      have ha : raw30736step2 = -raw30736step1 := by apply Matrix.ext; change ∀ i j, raw30736step2 i j = -(raw30736step1 i j); unfold raw30736step2 raw30736step1; decide +kernel
      have hl : raw30736step2Labels = raw30736step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30736step2 raw30736step2Labels = mixedMoment B raw30736step3 raw30736step3Labels := by
      have ha : raw30736step3 = raw30736step2 := by apply Matrix.ext; unfold raw30736step3 raw30736step2; decide +kernel
      have hl : raw30736step2Labels = labelEmbedding1 ∘ raw30736step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30736step2 raw30736step2Labels raw30736step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

def raw30737 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30737Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30737step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30737step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30737step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30737step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30737step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30737step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30737step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30737step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30737 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30737 raw30737Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw30737 raw30737Labels = mixedMoment B raw30737step0 raw30737step0Labels := by
      have hz : ∀ j, raw30737 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30737step0 = (fun i j => raw30737 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30737step0 raw30737; decide +kernel
      have hl : raw30737step0Labels = raw30737Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30737 raw30737Labels permutation346 hz
    mixedMoment B raw30737step0 raw30737step0Labels = mixedMoment B raw30737step1 raw30737step1Labels := by
      have ha : raw30737step1 = (fun i j => raw30737step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30737step1 raw30737step0; decide +kernel
      have hl : raw30737step1Labels = raw30737step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30737step0 raw30737step0Labels permutation33 permutation7
    mixedMoment B raw30737step1 raw30737step1Labels = mixedMoment B raw30737step2 raw30737step2Labels := by
      have ha : raw30737step2 = -raw30737step1 := by apply Matrix.ext; change ∀ i j, raw30737step2 i j = -(raw30737step1 i j); unfold raw30737step2 raw30737step1; decide +kernel
      have hl : raw30737step2Labels = raw30737step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30737step2 raw30737step2Labels = mixedMoment B raw30737step3 raw30737step3Labels := by
      have ha : raw30737step3 = raw30737step2 := by apply Matrix.ext; unfold raw30737step3 raw30737step2; decide +kernel
      have hl : raw30737step2Labels = labelEmbedding1 ∘ raw30737step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30737step2 raw30737step2Labels raw30737step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

def raw30738 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30738Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30738step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30738step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30738step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw30738step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30738step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw30738step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30738step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30738step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30738step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30738step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30738 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30738 raw30738Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw30738 raw30738Labels = mixedMoment B raw30738step0 raw30738step0Labels := by
      have hz : ∀ j, raw30738 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30738step0 = (fun i j => raw30738 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30738step0 raw30738; decide +kernel
      have hl : raw30738step0Labels = raw30738Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30738 raw30738Labels permutation434 hz
    mixedMoment B raw30738step0 raw30738step0Labels = mixedMoment B raw30738step1 raw30738step1Labels := by
      have hz : ∀ j, raw30738step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30738step1 = (fun i j => raw30738step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30738step1 raw30738step0; decide +kernel
      have hl : raw30738step1Labels = raw30738step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30738step0 raw30738step0Labels permutation80 hz
    mixedMoment B raw30738step1 raw30738step1Labels = mixedMoment B raw30738step2 raw30738step2Labels := by
      have ha : raw30738step2 = (fun i j => raw30738step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30738step2 raw30738step1; decide +kernel
      have hl : raw30738step2Labels = raw30738step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30738step1 raw30738step1Labels permutation9 permutation7
    mixedMoment B raw30738step2 raw30738step2Labels = mixedMoment B raw30738step3 raw30738step3Labels := by
      have ha : raw30738step3 = -raw30738step2 := by apply Matrix.ext; change ∀ i j, raw30738step3 i j = -(raw30738step2 i j); unfold raw30738step3 raw30738step2; decide +kernel
      have hl : raw30738step3Labels = raw30738step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30738step3 raw30738step3Labels = mixedMoment B raw30738step4 raw30738step4Labels := by
      have ha : raw30738step4 = raw30738step3 := by apply Matrix.ext; unfold raw30738step4 raw30738step3; decide +kernel
      have hl : raw30738step3Labels = labelEmbedding1 ∘ raw30738step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30738step3 raw30738step3Labels raw30738step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3547 node3547Labels := by rfl

def raw30739 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30739Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30739step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30739step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30739step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30739step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30739step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30739step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30739step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30739step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30739 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30739 raw30739Labels = mixedMoment B node3265 node3265Labels := by
  calc
    mixedMoment B raw30739 raw30739Labels = mixedMoment B raw30739step0 raw30739step0Labels := by
      have hz : ∀ j, raw30739 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30739step0 = (fun i j => raw30739 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30739step0 raw30739; decide +kernel
      have hl : raw30739step0Labels = raw30739Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30739 raw30739Labels permutation434 hz
    mixedMoment B raw30739step0 raw30739step0Labels = mixedMoment B raw30739step1 raw30739step1Labels := by
      have ha : raw30739step1 = (fun i j => raw30739step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30739step1 raw30739step0; decide +kernel
      have hl : raw30739step1Labels = raw30739step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30739step0 raw30739step0Labels permutation33 permutation7
    mixedMoment B raw30739step1 raw30739step1Labels = mixedMoment B raw30739step2 raw30739step2Labels := by
      have ha : raw30739step2 = -raw30739step1 := by apply Matrix.ext; change ∀ i j, raw30739step2 i j = -(raw30739step1 i j); unfold raw30739step2 raw30739step1; decide +kernel
      have hl : raw30739step2Labels = raw30739step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30739step2 raw30739step2Labels = mixedMoment B raw30739step3 raw30739step3Labels := by
      have ha : raw30739step3 = raw30739step2 := by apply Matrix.ext; unfold raw30739step3 raw30739step2; decide +kernel
      have hl : raw30739step2Labels = labelEmbedding1 ∘ raw30739step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30739step2 raw30739step2Labels raw30739step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3265 node3265Labels := by rfl

def raw30740 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30740Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30740step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30740step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30740step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30740step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30740step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30740step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30740step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30740step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30740 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30740 raw30740Labels = mixedMoment B node3412 node3412Labels := by
  calc
    mixedMoment B raw30740 raw30740Labels = mixedMoment B raw30740step0 raw30740step0Labels := by
      have hz : ∀ j, raw30740 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30740step0 = (fun i j => raw30740 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30740step0 raw30740; decide +kernel
      have hl : raw30740step0Labels = raw30740Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30740 raw30740Labels permutation434 hz
    mixedMoment B raw30740step0 raw30740step0Labels = mixedMoment B raw30740step1 raw30740step1Labels := by
      have ha : raw30740step1 = (fun i j => raw30740step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30740step1 raw30740step0; decide +kernel
      have hl : raw30740step1Labels = raw30740step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30740step0 raw30740step0Labels permutation33 permutation7
    mixedMoment B raw30740step1 raw30740step1Labels = mixedMoment B raw30740step2 raw30740step2Labels := by
      have ha : raw30740step2 = -raw30740step1 := by apply Matrix.ext; change ∀ i j, raw30740step2 i j = -(raw30740step1 i j); unfold raw30740step2 raw30740step1; decide +kernel
      have hl : raw30740step2Labels = raw30740step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30740step2 raw30740step2Labels = mixedMoment B raw30740step3 raw30740step3Labels := by
      have ha : raw30740step3 = raw30740step2 := by apply Matrix.ext; unfold raw30740step3 raw30740step2; decide +kernel
      have hl : raw30740step2Labels = labelEmbedding1 ∘ raw30740step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30740step2 raw30740step2Labels raw30740step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3412 node3412Labels := by rfl

def raw30741 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30741Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30741step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30741step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30741step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30741step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30741step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30741step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30741 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30741 raw30741Labels = mixedMoment B node3450 node3450Labels := by
  calc
    mixedMoment B raw30741 raw30741Labels = mixedMoment B raw30741step0 raw30741step0Labels := by
      have ha : raw30741step0 = (fun i j => raw30741 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30741step0 raw30741; decide +kernel
      have hl : raw30741step0Labels = raw30741Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30741 raw30741Labels permutation159 permutation7
    mixedMoment B raw30741step0 raw30741step0Labels = mixedMoment B raw30741step1 raw30741step1Labels := by
      have ha : raw30741step1 = -raw30741step0 := by apply Matrix.ext; change ∀ i j, raw30741step1 i j = -(raw30741step0 i j); unfold raw30741step1 raw30741step0; decide +kernel
      have hl : raw30741step1Labels = raw30741step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30741step1 raw30741step1Labels = mixedMoment B raw30741step2 raw30741step2Labels := by
      have ha : raw30741step2 = raw30741step1 := by apply Matrix.ext; unfold raw30741step2 raw30741step1; decide +kernel
      have hl : raw30741step1Labels = labelEmbedding1 ∘ raw30741step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30741step1 raw30741step1Labels raw30741step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3450 node3450Labels := by rfl

def raw30742 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30742Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30742step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30742step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30742step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw30742step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30742step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw30742step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30742step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw30742step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30742 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30742 raw30742Labels = mixedMoment B node3471 node3471Labels := by
  calc
    mixedMoment B raw30742 raw30742Labels = mixedMoment B raw30742step0 raw30742step0Labels := by
      have hz : ∀ j, raw30742 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30742step0 = (fun i j => raw30742 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30742step0 raw30742; decide +kernel
      have hl : raw30742step0Labels = raw30742Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30742 raw30742Labels permutation434 hz
    mixedMoment B raw30742step0 raw30742step0Labels = mixedMoment B raw30742step1 raw30742step1Labels := by
      have ha : raw30742step1 = (fun i j => raw30742step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30742step1 raw30742step0; decide +kernel
      have hl : raw30742step1Labels = raw30742step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30742step0 raw30742step0Labels permutation33 permutation7
    mixedMoment B raw30742step1 raw30742step1Labels = mixedMoment B raw30742step2 raw30742step2Labels := by
      have ha : raw30742step2 = -raw30742step1 := by apply Matrix.ext; change ∀ i j, raw30742step2 i j = -(raw30742step1 i j); unfold raw30742step2 raw30742step1; decide +kernel
      have hl : raw30742step2Labels = raw30742step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30742step2 raw30742step2Labels = mixedMoment B raw30742step3 raw30742step3Labels := by
      have ha : raw30742step3 = raw30742step2 := by apply Matrix.ext; unfold raw30742step3 raw30742step2; decide +kernel
      have hl : raw30742step2Labels = labelEmbedding1 ∘ raw30742step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30742step2 raw30742step2Labels raw30742step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3471 node3471Labels := by rfl

def raw30743 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30743Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30743step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30743step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30743step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30743step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30743step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30743step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30743step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30743step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30743 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30743 raw30743Labels = mixedMoment B node3470 node3470Labels := by
  calc
    mixedMoment B raw30743 raw30743Labels = mixedMoment B raw30743step0 raw30743step0Labels := by
      have hz : ∀ j, raw30743 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30743step0 = (fun i j => raw30743 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30743step0 raw30743; decide +kernel
      have hl : raw30743step0Labels = raw30743Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30743 raw30743Labels permutation434 hz
    mixedMoment B raw30743step0 raw30743step0Labels = mixedMoment B raw30743step1 raw30743step1Labels := by
      have ha : raw30743step1 = (fun i j => raw30743step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30743step1 raw30743step0; decide +kernel
      have hl : raw30743step1Labels = raw30743step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30743step0 raw30743step0Labels permutation33 permutation7
    mixedMoment B raw30743step1 raw30743step1Labels = mixedMoment B raw30743step2 raw30743step2Labels := by
      have ha : raw30743step2 = -raw30743step1 := by apply Matrix.ext; change ∀ i j, raw30743step2 i j = -(raw30743step1 i j); unfold raw30743step2 raw30743step1; decide +kernel
      have hl : raw30743step2Labels = raw30743step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30743step2 raw30743step2Labels = mixedMoment B raw30743step3 raw30743step3Labels := by
      have ha : raw30743step3 = raw30743step2 := by apply Matrix.ext; unfold raw30743step3 raw30743step2; decide +kernel
      have hl : raw30743step2Labels = labelEmbedding1 ∘ raw30743step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30743step2 raw30743step2Labels raw30743step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3470 node3470Labels := by rfl

def raw30744 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30744Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30744step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30744step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30744step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30744step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30744step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30744step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30744step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30744step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30744 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30744 raw30744Labels = mixedMoment B node3265 node3265Labels := by
  calc
    mixedMoment B raw30744 raw30744Labels = mixedMoment B raw30744step0 raw30744step0Labels := by
      have hz : ∀ j, raw30744 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30744step0 = (fun i j => raw30744 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30744step0 raw30744; decide +kernel
      have hl : raw30744step0Labels = raw30744Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30744 raw30744Labels permutation346 hz
    mixedMoment B raw30744step0 raw30744step0Labels = mixedMoment B raw30744step1 raw30744step1Labels := by
      have ha : raw30744step1 = (fun i j => raw30744step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30744step1 raw30744step0; decide +kernel
      have hl : raw30744step1Labels = raw30744step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30744step0 raw30744step0Labels permutation33 permutation7
    mixedMoment B raw30744step1 raw30744step1Labels = mixedMoment B raw30744step2 raw30744step2Labels := by
      have ha : raw30744step2 = -raw30744step1 := by apply Matrix.ext; change ∀ i j, raw30744step2 i j = -(raw30744step1 i j); unfold raw30744step2 raw30744step1; decide +kernel
      have hl : raw30744step2Labels = raw30744step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30744step2 raw30744step2Labels = mixedMoment B raw30744step3 raw30744step3Labels := by
      have ha : raw30744step3 = raw30744step2 := by apply Matrix.ext; unfold raw30744step3 raw30744step2; decide +kernel
      have hl : raw30744step2Labels = labelEmbedding1 ∘ raw30744step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30744step2 raw30744step2Labels raw30744step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3265 node3265Labels := by rfl

def raw30745 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30745Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30745step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30745step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30745step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30745step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30745step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30745step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30745step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30745step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30745 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30745 raw30745Labels = mixedMoment B node3412 node3412Labels := by
  calc
    mixedMoment B raw30745 raw30745Labels = mixedMoment B raw30745step0 raw30745step0Labels := by
      have hz : ∀ j, raw30745 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30745step0 = (fun i j => raw30745 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30745step0 raw30745; decide +kernel
      have hl : raw30745step0Labels = raw30745Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30745 raw30745Labels permutation346 hz
    mixedMoment B raw30745step0 raw30745step0Labels = mixedMoment B raw30745step1 raw30745step1Labels := by
      have ha : raw30745step1 = (fun i j => raw30745step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30745step1 raw30745step0; decide +kernel
      have hl : raw30745step1Labels = raw30745step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30745step0 raw30745step0Labels permutation33 permutation7
    mixedMoment B raw30745step1 raw30745step1Labels = mixedMoment B raw30745step2 raw30745step2Labels := by
      have ha : raw30745step2 = -raw30745step1 := by apply Matrix.ext; change ∀ i j, raw30745step2 i j = -(raw30745step1 i j); unfold raw30745step2 raw30745step1; decide +kernel
      have hl : raw30745step2Labels = raw30745step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30745step2 raw30745step2Labels = mixedMoment B raw30745step3 raw30745step3Labels := by
      have ha : raw30745step3 = raw30745step2 := by apply Matrix.ext; unfold raw30745step3 raw30745step2; decide +kernel
      have hl : raw30745step2Labels = labelEmbedding1 ∘ raw30745step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30745step2 raw30745step2Labels raw30745step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3412 node3412Labels := by rfl

def raw30746 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -1, -1]]
def raw30746Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30746step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw30746step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30746step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30746step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30746step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw30746step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30746 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30746 raw30746Labels = mixedMoment B node3450 node3450Labels := by
  calc
    mixedMoment B raw30746 raw30746Labels = mixedMoment B raw30746step0 raw30746step0Labels := by
      have ha : raw30746step0 = (fun i j => raw30746 (permutation153 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30746step0 raw30746; decide +kernel
      have hl : raw30746step0Labels = raw30746Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30746 raw30746Labels permutation153 permutation7
    mixedMoment B raw30746step0 raw30746step0Labels = mixedMoment B raw30746step1 raw30746step1Labels := by
      have ha : raw30746step1 = -raw30746step0 := by apply Matrix.ext; change ∀ i j, raw30746step1 i j = -(raw30746step0 i j); unfold raw30746step1 raw30746step0; decide +kernel
      have hl : raw30746step1Labels = raw30746step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30746step1 raw30746step1Labels = mixedMoment B raw30746step2 raw30746step2Labels := by
      have ha : raw30746step2 = raw30746step1 := by apply Matrix.ext; unfold raw30746step2 raw30746step1; decide +kernel
      have hl : raw30746step1Labels = labelEmbedding1 ∘ raw30746step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30746step1 raw30746step1Labels raw30746step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3450 node3450Labels := by rfl

def raw30747 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30747Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30747step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw30747step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30747step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw30747step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30747step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw30747step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30747step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw30747step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30747 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30747 raw30747Labels = mixedMoment B node3471 node3471Labels := by
  calc
    mixedMoment B raw30747 raw30747Labels = mixedMoment B raw30747step0 raw30747step0Labels := by
      have hz : ∀ j, raw30747 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30747step0 = (fun i j => raw30747 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30747step0 raw30747; decide +kernel
      have hl : raw30747step0Labels = raw30747Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30747 raw30747Labels permutation346 hz
    mixedMoment B raw30747step0 raw30747step0Labels = mixedMoment B raw30747step1 raw30747step1Labels := by
      have ha : raw30747step1 = (fun i j => raw30747step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30747step1 raw30747step0; decide +kernel
      have hl : raw30747step1Labels = raw30747step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30747step0 raw30747step0Labels permutation33 permutation7
    mixedMoment B raw30747step1 raw30747step1Labels = mixedMoment B raw30747step2 raw30747step2Labels := by
      have ha : raw30747step2 = -raw30747step1 := by apply Matrix.ext; change ∀ i j, raw30747step2 i j = -(raw30747step1 i j); unfold raw30747step2 raw30747step1; decide +kernel
      have hl : raw30747step2Labels = raw30747step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30747step2 raw30747step2Labels = mixedMoment B raw30747step3 raw30747step3Labels := by
      have ha : raw30747step3 = raw30747step2 := by apply Matrix.ext; unfold raw30747step3 raw30747step2; decide +kernel
      have hl : raw30747step2Labels = labelEmbedding1 ∘ raw30747step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30747step2 raw30747step2Labels raw30747step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3471 node3471Labels := by rfl

def raw30748 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30748Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30748step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![1, 0, -1]]
def raw30748step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30748step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30748step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30748step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30748step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30748step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30748step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30748 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30748 raw30748Labels = mixedMoment B node3470 node3470Labels := by
  calc
    mixedMoment B raw30748 raw30748Labels = mixedMoment B raw30748step0 raw30748step0Labels := by
      have hz : ∀ j, raw30748 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30748step0 = (fun i j => raw30748 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30748step0 raw30748; decide +kernel
      have hl : raw30748step0Labels = raw30748Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30748 raw30748Labels permutation346 hz
    mixedMoment B raw30748step0 raw30748step0Labels = mixedMoment B raw30748step1 raw30748step1Labels := by
      have ha : raw30748step1 = (fun i j => raw30748step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30748step1 raw30748step0; decide +kernel
      have hl : raw30748step1Labels = raw30748step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30748step0 raw30748step0Labels permutation33 permutation7
    mixedMoment B raw30748step1 raw30748step1Labels = mixedMoment B raw30748step2 raw30748step2Labels := by
      have ha : raw30748step2 = -raw30748step1 := by apply Matrix.ext; change ∀ i j, raw30748step2 i j = -(raw30748step1 i j); unfold raw30748step2 raw30748step1; decide +kernel
      have hl : raw30748step2Labels = raw30748step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30748step2 raw30748step2Labels = mixedMoment B raw30748step3 raw30748step3Labels := by
      have ha : raw30748step3 = raw30748step2 := by apply Matrix.ext; unfold raw30748step3 raw30748step2; decide +kernel
      have hl : raw30748step2Labels = labelEmbedding1 ∘ raw30748step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30748step2 raw30748step2Labels raw30748step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3470 node3470Labels := by rfl

def raw30749 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30749Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30749step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30749step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30749step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30749step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30749step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -1, 2], ![-2, -1, 3]]
def raw30749step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30749step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw30749step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30749step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 1, -2], ![2, 1, -3]]
def raw30749step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30749 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30749 raw30749Labels = mixedMoment B node3276 node3276Labels := by
  calc
    mixedMoment B raw30749 raw30749Labels = mixedMoment B raw30749step0 raw30749step0Labels := by
      have hz : ∀ j, raw30749 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30749step0 = (fun i j => raw30749 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30749step0 raw30749; decide +kernel
      have hl : raw30749step0Labels = raw30749Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30749 raw30749Labels permutation434 hz
    mixedMoment B raw30749step0 raw30749step0Labels = mixedMoment B raw30749step1 raw30749step1Labels := by
      have hz : ∀ j, raw30749step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30749step1 = (fun i j => raw30749step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30749step1 raw30749step0; decide +kernel
      have hl : raw30749step1Labels = raw30749step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30749step0 raw30749step0Labels permutation80 hz
    mixedMoment B raw30749step1 raw30749step1Labels = mixedMoment B raw30749step2 raw30749step2Labels := by
      have ha : raw30749step2 = (fun i j => raw30749step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30749step2 raw30749step1; decide +kernel
      have hl : raw30749step2Labels = raw30749step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30749step1 raw30749step1Labels permutation9 permutation7
    mixedMoment B raw30749step2 raw30749step2Labels = mixedMoment B raw30749step3 raw30749step3Labels := by
      have ha : raw30749step3 = -raw30749step2 := by apply Matrix.ext; change ∀ i j, raw30749step3 i j = -(raw30749step2 i j); unfold raw30749step3 raw30749step2; decide +kernel
      have hl : raw30749step3Labels = raw30749step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30749step3 raw30749step3Labels = mixedMoment B raw30749step4 raw30749step4Labels := by
      have ha : raw30749step4 = raw30749step3 := by apply Matrix.ext; unfold raw30749step4 raw30749step3; decide +kernel
      have hl : raw30749step3Labels = labelEmbedding1 ∘ raw30749step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30749step3 raw30749step3Labels raw30749step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3276 node3276Labels := by rfl

def raw30750 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30750Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30750step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30750step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30750step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![3, -1, -2], ![2, -1, -1]]
def raw30750step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30750step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 1, -2], ![2, 1, -3]]
def raw30750step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30750step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 1, -2], ![2, 1, -3]]
def raw30750step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30750 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30750 raw30750Labels = mixedMoment B node3422 node3422Labels := by
  calc
    mixedMoment B raw30750 raw30750Labels = mixedMoment B raw30750step0 raw30750step0Labels := by
      have hz : ∀ j, raw30750 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30750step0 = (fun i j => raw30750 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30750step0 raw30750; decide +kernel
      have hl : raw30750step0Labels = raw30750Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30750 raw30750Labels permutation434 hz
    mixedMoment B raw30750step0 raw30750step0Labels = mixedMoment B raw30750step1 raw30750step1Labels := by
      have hz : ∀ j, raw30750step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30750step1 = (fun i j => raw30750step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30750step1 raw30750step0; decide +kernel
      have hl : raw30750step1Labels = raw30750step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30750step0 raw30750step0Labels permutation80 hz
    mixedMoment B raw30750step1 raw30750step1Labels = mixedMoment B raw30750step2 raw30750step2Labels := by
      have ha : raw30750step2 = (fun i j => raw30750step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30750step2 raw30750step1; decide +kernel
      have hl : raw30750step2Labels = raw30750step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30750step1 raw30750step1Labels permutation25 permutation7
    mixedMoment B raw30750step2 raw30750step2Labels = mixedMoment B raw30750step3 raw30750step3Labels := by
      have ha : raw30750step3 = raw30750step2 := by apply Matrix.ext; unfold raw30750step3 raw30750step2; decide +kernel
      have hl : raw30750step2Labels = labelEmbedding1 ∘ raw30750step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30750step2 raw30750step2Labels raw30750step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3422 node3422Labels := by rfl

def raw30751 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30751Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30751step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30751step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30751step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30751step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30751step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30751step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30751 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30751 raw30751Labels = mixedMoment B node3411 node3411Labels := by
  calc
    mixedMoment B raw30751 raw30751Labels = mixedMoment B raw30751step0 raw30751step0Labels := by
      have hz : ∀ j, raw30751 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30751step0 = (fun i j => raw30751 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30751step0 raw30751; decide +kernel
      have hl : raw30751step0Labels = raw30751Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30751 raw30751Labels permutation434 hz
    mixedMoment B raw30751step0 raw30751step0Labels = mixedMoment B raw30751step1 raw30751step1Labels := by
      have ha : raw30751step1 = (fun i j => raw30751step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30751step1 raw30751step0; decide +kernel
      have hl : raw30751step1Labels = raw30751step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30751step0 raw30751step0Labels permutation127 permutation7
    mixedMoment B raw30751step1 raw30751step1Labels = mixedMoment B raw30751step2 raw30751step2Labels := by
      have ha : raw30751step2 = raw30751step1 := by apply Matrix.ext; unfold raw30751step2 raw30751step1; decide +kernel
      have hl : raw30751step1Labels = labelEmbedding1 ∘ raw30751step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30751step1 raw30751step1Labels raw30751step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3411 node3411Labels := by rfl

def raw30752 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30752Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30752step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![3, -1, -2], ![2, -1, -1]]
def raw30752step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30752step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30752step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30752step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30752step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30752 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30752 raw30752Labels = mixedMoment B node3411 node3411Labels := by
  calc
    mixedMoment B raw30752 raw30752Labels = mixedMoment B raw30752step0 raw30752step0Labels := by
      have hz : ∀ j, raw30752 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30752step0 = (fun i j => raw30752 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30752step0 raw30752; decide +kernel
      have hl : raw30752step0Labels = raw30752Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30752 raw30752Labels permutation346 hz
    mixedMoment B raw30752step0 raw30752step0Labels = mixedMoment B raw30752step1 raw30752step1Labels := by
      have ha : raw30752step1 = (fun i j => raw30752step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30752step1 raw30752step0; decide +kernel
      have hl : raw30752step1Labels = raw30752step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30752step0 raw30752step0Labels permutation127 permutation7
    mixedMoment B raw30752step1 raw30752step1Labels = mixedMoment B raw30752step2 raw30752step2Labels := by
      have ha : raw30752step2 = raw30752step1 := by apply Matrix.ext; unfold raw30752step2 raw30752step1; decide +kernel
      have hl : raw30752step1Labels = labelEmbedding1 ∘ raw30752step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30752step1 raw30752step1Labels raw30752step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3411 node3411Labels := by rfl

def raw30753 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw30753Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30753step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![3, -1, -2], ![1, 0, -1]]
def raw30753step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30753step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![3, -1, -2], ![1, 0, -1]]
def raw30753step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30753step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30753step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30753step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, 1, -3]]
def raw30753step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30753 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30753 raw30753Labels = mixedMoment B node3484 node3484Labels := by
  calc
    mixedMoment B raw30753 raw30753Labels = mixedMoment B raw30753step0 raw30753step0Labels := by
      have hz : ∀ j, raw30753 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30753step0 = (fun i j => raw30753 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30753step0 raw30753; decide +kernel
      have hl : raw30753step0Labels = raw30753Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30753 raw30753Labels permutation434 hz
    mixedMoment B raw30753step0 raw30753step0Labels = mixedMoment B raw30753step1 raw30753step1Labels := by
      have hz : ∀ j, raw30753step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30753step1 = (fun i j => raw30753step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30753step1 raw30753step0; decide +kernel
      have hl : raw30753step1Labels = raw30753step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30753step0 raw30753step0Labels permutation80 hz
    mixedMoment B raw30753step1 raw30753step1Labels = mixedMoment B raw30753step2 raw30753step2Labels := by
      have ha : raw30753step2 = (fun i j => raw30753step1 (permutation25 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30753step2 raw30753step1; decide +kernel
      have hl : raw30753step2Labels = raw30753step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30753step1 raw30753step1Labels permutation25 permutation7
    mixedMoment B raw30753step2 raw30753step2Labels = mixedMoment B raw30753step3 raw30753step3Labels := by
      have ha : raw30753step3 = raw30753step2 := by apply Matrix.ext; unfold raw30753step3 raw30753step2; decide +kernel
      have hl : raw30753step2Labels = labelEmbedding1 ∘ raw30753step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30753step2 raw30753step2Labels raw30753step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3484 node3484Labels := by rfl

def raw30754 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30754Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30754step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30754step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30754step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30754step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30754step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw30754step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30754step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw30754step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30754step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 2, -3], ![2, 0, -2]]
def raw30754step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30754 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30754 raw30754Labels = mixedMoment B node3277 node3277Labels := by
  calc
    mixedMoment B raw30754 raw30754Labels = mixedMoment B raw30754step0 raw30754step0Labels := by
      have hz : ∀ j, raw30754 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30754step0 = (fun i j => raw30754 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30754step0 raw30754; decide +kernel
      have hl : raw30754step0Labels = raw30754Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30754 raw30754Labels permutation434 hz
    mixedMoment B raw30754step0 raw30754step0Labels = mixedMoment B raw30754step1 raw30754step1Labels := by
      have hz : ∀ j, raw30754step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30754step1 = (fun i j => raw30754step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30754step1 raw30754step0; decide +kernel
      have hl : raw30754step1Labels = raw30754step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30754step0 raw30754step0Labels permutation80 hz
    mixedMoment B raw30754step1 raw30754step1Labels = mixedMoment B raw30754step2 raw30754step2Labels := by
      have ha : raw30754step2 = (fun i j => raw30754step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30754step2 raw30754step1; decide +kernel
      have hl : raw30754step2Labels = raw30754step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30754step1 raw30754step1Labels permutation9 permutation7
    mixedMoment B raw30754step2 raw30754step2Labels = mixedMoment B raw30754step3 raw30754step3Labels := by
      have ha : raw30754step3 = -raw30754step2 := by apply Matrix.ext; change ∀ i j, raw30754step3 i j = -(raw30754step2 i j); unfold raw30754step3 raw30754step2; decide +kernel
      have hl : raw30754step3Labels = raw30754step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30754step3 raw30754step3Labels = mixedMoment B raw30754step4 raw30754step4Labels := by
      have ha : raw30754step4 = raw30754step3 := by apply Matrix.ext; unfold raw30754step4 raw30754step3; decide +kernel
      have hl : raw30754step3Labels = labelEmbedding1 ∘ raw30754step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30754step3 raw30754step3Labels raw30754step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3277 node3277Labels := by rfl

def raw30755 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30755Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30755step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30755step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30755step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw30755step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30755step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, -2, 3], ![-2, 0, 2]]
def raw30755step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30755step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw30755step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30755step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 2, -3], ![2, 0, -2]]
def raw30755step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30755 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30755 raw30755Labels = mixedMoment B node3423 node3423Labels := by
  calc
    mixedMoment B raw30755 raw30755Labels = mixedMoment B raw30755step0 raw30755step0Labels := by
      have hz : ∀ j, raw30755 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30755step0 = (fun i j => raw30755 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30755step0 raw30755; decide +kernel
      have hl : raw30755step0Labels = raw30755Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30755 raw30755Labels permutation434 hz
    mixedMoment B raw30755step0 raw30755step0Labels = mixedMoment B raw30755step1 raw30755step1Labels := by
      have hz : ∀ j, raw30755step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30755step1 = (fun i j => raw30755step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30755step1 raw30755step0; decide +kernel
      have hl : raw30755step1Labels = raw30755step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30755step0 raw30755step0Labels permutation80 hz
    mixedMoment B raw30755step1 raw30755step1Labels = mixedMoment B raw30755step2 raw30755step2Labels := by
      have ha : raw30755step2 = (fun i j => raw30755step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30755step2 raw30755step1; decide +kernel
      have hl : raw30755step2Labels = raw30755step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30755step1 raw30755step1Labels permutation9 permutation7
    mixedMoment B raw30755step2 raw30755step2Labels = mixedMoment B raw30755step3 raw30755step3Labels := by
      have ha : raw30755step3 = -raw30755step2 := by apply Matrix.ext; change ∀ i j, raw30755step3 i j = -(raw30755step2 i j); unfold raw30755step3 raw30755step2; decide +kernel
      have hl : raw30755step3Labels = raw30755step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30755step3 raw30755step3Labels = mixedMoment B raw30755step4 raw30755step4Labels := by
      have ha : raw30755step4 = raw30755step3 := by apply Matrix.ext; unfold raw30755step4 raw30755step3; decide +kernel
      have hl : raw30755step3Labels = labelEmbedding1 ∘ raw30755step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30755step3 raw30755step3Labels raw30755step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3423 node3423Labels := by rfl

def raw30756 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30756Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30756step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30756step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30756step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw30756step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30756step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw30756step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30756step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw30756step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30756 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30756 raw30756Labels = mixedMoment B node3457 node3457Labels := by
  calc
    mixedMoment B raw30756 raw30756Labels = mixedMoment B raw30756step0 raw30756step0Labels := by
      have hz : ∀ j, raw30756 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30756step0 = (fun i j => raw30756 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30756step0 raw30756; decide +kernel
      have hl : raw30756step0Labels = raw30756Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30756 raw30756Labels permutation434 hz
    mixedMoment B raw30756step0 raw30756step0Labels = mixedMoment B raw30756step1 raw30756step1Labels := by
      have ha : raw30756step1 = (fun i j => raw30756step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30756step1 raw30756step0; decide +kernel
      have hl : raw30756step1Labels = raw30756step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30756step0 raw30756step0Labels permutation33 permutation7
    mixedMoment B raw30756step1 raw30756step1Labels = mixedMoment B raw30756step2 raw30756step2Labels := by
      have ha : raw30756step2 = -raw30756step1 := by apply Matrix.ext; change ∀ i j, raw30756step2 i j = -(raw30756step1 i j); unfold raw30756step2 raw30756step1; decide +kernel
      have hl : raw30756step2Labels = raw30756step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30756step2 raw30756step2Labels = mixedMoment B raw30756step3 raw30756step3Labels := by
      have ha : raw30756step3 = raw30756step2 := by apply Matrix.ext; unfold raw30756step3 raw30756step2; decide +kernel
      have hl : raw30756step2Labels = labelEmbedding1 ∘ raw30756step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30756step2 raw30756step2Labels raw30756step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3457 node3457Labels := by rfl

def raw30757 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30757Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30757step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30757step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30757step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, -2, 3], ![-2, 0, 2]]
def raw30757step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30757step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw30757step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30757step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw30757step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30757 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30757 raw30757Labels = mixedMoment B node3457 node3457Labels := by
  calc
    mixedMoment B raw30757 raw30757Labels = mixedMoment B raw30757step0 raw30757step0Labels := by
      have hz : ∀ j, raw30757 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30757step0 = (fun i j => raw30757 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30757step0 raw30757; decide +kernel
      have hl : raw30757step0Labels = raw30757Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30757 raw30757Labels permutation346 hz
    mixedMoment B raw30757step0 raw30757step0Labels = mixedMoment B raw30757step1 raw30757step1Labels := by
      have ha : raw30757step1 = (fun i j => raw30757step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30757step1 raw30757step0; decide +kernel
      have hl : raw30757step1Labels = raw30757step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30757step0 raw30757step0Labels permutation33 permutation7
    mixedMoment B raw30757step1 raw30757step1Labels = mixedMoment B raw30757step2 raw30757step2Labels := by
      have ha : raw30757step2 = -raw30757step1 := by apply Matrix.ext; change ∀ i j, raw30757step2 i j = -(raw30757step1 i j); unfold raw30757step2 raw30757step1; decide +kernel
      have hl : raw30757step2Labels = raw30757step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30757step2 raw30757step2Labels = mixedMoment B raw30757step3 raw30757step3Labels := by
      have ha : raw30757step3 = raw30757step2 := by apply Matrix.ext; unfold raw30757step3 raw30757step2; decide +kernel
      have hl : raw30757step2Labels = labelEmbedding1 ∘ raw30757step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30757step2 raw30757step2Labels raw30757step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3457 node3457Labels := by rfl

def raw30758 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw30758Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30758step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw30758step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30758step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw30758step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30758step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw30758step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30758 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30758 raw30758Labels = mixedMoment B node3356 node3356Labels := by
  calc
    mixedMoment B raw30758 raw30758Labels = mixedMoment B raw30758step0 raw30758step0Labels := by
      have hz : ∀ j, raw30758 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30758step0 = (fun i j => raw30758 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30758step0 raw30758; decide +kernel
      have hl : raw30758step0Labels = raw30758Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30758 raw30758Labels permutation346 hz
    mixedMoment B raw30758step0 raw30758step0Labels = mixedMoment B raw30758step1 raw30758step1Labels := by
      have ha : raw30758step1 = (fun i j => raw30758step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30758step1 raw30758step0; decide +kernel
      have hl : raw30758step1Labels = raw30758step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30758step0 raw30758step0Labels permutation125 permutation2
    mixedMoment B raw30758step1 raw30758step1Labels = mixedMoment B raw30758step2 raw30758step2Labels := by
      have ha : raw30758step2 = -raw30758step1 := by apply Matrix.ext; change ∀ i j, raw30758step2 i j = -(raw30758step1 i j); unfold raw30758step2 raw30758step1; decide +kernel
      have hl : raw30758step2Labels = raw30758step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3356 node3356Labels := by rfl

def raw30759 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw30759Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30759step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw30759step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30759step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw30759step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30759 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30759 raw30759Labels = mixedMoment B node2467 node2467Labels := by
  calc
    mixedMoment B raw30759 raw30759Labels = mixedMoment B raw30759step0 raw30759step0Labels := by
      have hz : ∀ j, raw30759 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30759step0 = (fun i j => raw30759 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30759step0 raw30759; decide +kernel
      have hl : raw30759step0Labels = raw30759Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30759 raw30759Labels permutation346 hz
    mixedMoment B raw30759step0 raw30759step0Labels = mixedMoment B raw30759step1 raw30759step1Labels := by
      have ha : raw30759step1 = (fun i j => raw30759step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30759step1 raw30759step0; decide +kernel
      have hl : raw30759step1Labels = raw30759step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30759step0 raw30759step0Labels permutation39 permutation2
    _ = mixedMoment B node2467 node2467Labels := by rfl

def raw30760 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 1, -3], ![2, -1, -1]]
def raw30760Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30760step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw30760step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30760 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30760 raw30760Labels = mixedMoment B node2413 node2413Labels := by
  calc
    mixedMoment B raw30760 raw30760Labels = mixedMoment B raw30760step0 raw30760step0Labels := by
      have ha : raw30760step0 = (fun i j => raw30760 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30760step0 raw30760; decide +kernel
      have hl : raw30760step0Labels = raw30760Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30760 raw30760Labels permutation159 permutation2
    _ = mixedMoment B node2413 node2413Labels := by rfl

def raw30761 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw30761Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30761step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw30761step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30761step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw30761step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30761 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30761 raw30761Labels = mixedMoment B node2467 node2467Labels := by
  calc
    mixedMoment B raw30761 raw30761Labels = mixedMoment B raw30761step0 raw30761step0Labels := by
      have hz : ∀ j, raw30761 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30761step0 = (fun i j => raw30761 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30761step0 raw30761; decide +kernel
      have hl : raw30761step0Labels = raw30761Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30761 raw30761Labels permutation346 hz
    mixedMoment B raw30761step0 raw30761step0Labels = mixedMoment B raw30761step1 raw30761step1Labels := by
      have ha : raw30761step1 = (fun i j => raw30761step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30761step1 raw30761step0; decide +kernel
      have hl : raw30761step1Labels = raw30761step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30761step0 raw30761step0Labels permutation33 permutation2
    _ = mixedMoment B node2467 node2467Labels := by rfl

def raw30762 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3], ![2, -1, -1]]
def raw30762Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30762step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![3, 0, -3], ![2, -1, -1]]
def raw30762step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30762step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30762step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30762step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw30762step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30762 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30762 raw30762Labels = mixedMoment B node1777 node1777Labels := by
  calc
    mixedMoment B raw30762 raw30762Labels = mixedMoment B raw30762step0 raw30762step0Labels := by
      have hz : ∀ j, raw30762 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30762step0 = (fun i j => raw30762 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30762step0 raw30762; decide +kernel
      have hl : raw30762step0Labels = raw30762Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30762 raw30762Labels permutation346 hz
    mixedMoment B raw30762step0 raw30762step0Labels = mixedMoment B raw30762step1 raw30762step1Labels := by
      have ha : raw30762step1 = (fun i j => raw30762step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30762step1 raw30762step0; decide +kernel
      have hl : raw30762step1Labels = raw30762step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30762step0 raw30762step0Labels permutation125 permutation2
    mixedMoment B raw30762step1 raw30762step1Labels = mixedMoment B raw30762step2 raw30762step2Labels := by
      have ha : raw30762step2 = -raw30762step1 := by apply Matrix.ext; change ∀ i j, raw30762step2 i j = -(raw30762step1 i j); unfold raw30762step2 raw30762step1; decide +kernel
      have hl : raw30762step2Labels = raw30762step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1777 node1777Labels := by rfl

def raw30763 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw30763Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30763step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw30763step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30763 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30763 raw30763Labels = mixedMoment B node2421 node2421Labels := by
  calc
    mixedMoment B raw30763 raw30763Labels = mixedMoment B raw30763step0 raw30763step0Labels := by
      have hz : ∀ j, raw30763 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30763step0 = (fun i j => raw30763 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30763step0 raw30763; decide +kernel
      have hl : raw30763step0Labels = raw30763Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30763 raw30763Labels permutation346 hz
    _ = mixedMoment B node2421 node2421Labels := by rfl

def raw30764 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![-1, 1], ![3, -3], ![1, -1]]
def raw30764Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30764step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![3, -3], ![1, -1]]
def raw30764step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30764step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw30764step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30764step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw30764step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical30764 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30764 raw30764Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw30764 raw30764Labels = mixedMoment B raw30764step0 raw30764step0Labels := by
      have hz : ∀ j, raw30764 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30764step0 = (fun i j => raw30764 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30764step0 raw30764; decide +kernel
      have hl : raw30764step0Labels = raw30764Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30764 raw30764Labels permutation346 hz
    mixedMoment B raw30764step0 raw30764step0Labels = mixedMoment B raw30764step1 raw30764step1Labels := by
      have ha : raw30764step1 = (fun i j => raw30764step0 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw30764step1 raw30764step0; decide +kernel
      have hl : raw30764step1Labels = raw30764step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30764step0 raw30764step0Labels permutation125 permutation0
    mixedMoment B raw30764step1 raw30764step1Labels = mixedMoment B raw30764step2 raw30764step2Labels := by
      have ha : raw30764step2 = -raw30764step1 := by apply Matrix.ext; change ∀ i j, raw30764step2 i j = -(raw30764step1 i j); unfold raw30764step2 raw30764step1; decide +kernel
      have hl : raw30764step2Labels = raw30764step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw30765 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30765Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30765step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30765step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30765step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw30765step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30765step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30765step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30765 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30765 raw30765Labels = mixedMoment B node5327 node5327Labels := by
  calc
    mixedMoment B raw30765 raw30765Labels = mixedMoment B raw30765step0 raw30765step0Labels := by
      have hz : ∀ j, raw30765 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30765step0 = (fun i j => raw30765 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30765step0 raw30765; decide +kernel
      have hl : raw30765step0Labels = raw30765Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30765 raw30765Labels permutation346 hz
    mixedMoment B raw30765step0 raw30765step0Labels = mixedMoment B raw30765step1 raw30765step1Labels := by
      have ha : raw30765step1 = (fun i j => raw30765step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30765step1 raw30765step0; decide +kernel
      have hl : raw30765step1Labels = raw30765step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30765step0 raw30765step0Labels permutation127 permutation2
    mixedMoment B raw30765step1 raw30765step1Labels = mixedMoment B raw30765step2 raw30765step2Labels := by
      have ha : raw30765step2 = -raw30765step1 := by apply Matrix.ext; change ∀ i j, raw30765step2 i j = -(raw30765step1 i j); unfold raw30765step2 raw30765step1; decide +kernel
      have hl : raw30765step2Labels = raw30765step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5327 node5327Labels := by rfl

def raw30766 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30766Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30766step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw30766step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30766step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30766step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30766 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30766 raw30766Labels = mixedMoment B node5323 node5323Labels := by
  calc
    mixedMoment B raw30766 raw30766Labels = mixedMoment B raw30766step0 raw30766step0Labels := by
      have ha : raw30766step0 = (fun i j => raw30766 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30766step0 raw30766; decide +kernel
      have hl : raw30766step0Labels = raw30766Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30766 raw30766Labels permutation589 permutation2
    mixedMoment B raw30766step0 raw30766step0Labels = mixedMoment B raw30766step1 raw30766step1Labels := by
      have ha : raw30766step1 = -raw30766step0 := by apply Matrix.ext; change ∀ i j, raw30766step1 i j = -(raw30766step0 i j); unfold raw30766step1 raw30766step0; decide +kernel
      have hl : raw30766step1Labels = raw30766step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5323 node5323Labels := by rfl

def raw30767 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30767Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30767step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30767step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30767step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw30767step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw30767step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw30767step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw30767step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw30767step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw30767step4 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw30767step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical30767 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30767 raw30767Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw30767 raw30767Labels = mixedMoment B raw30767step0 raw30767step0Labels := by
      have hz : ∀ j, raw30767 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30767step0 = (fun i j => raw30767 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30767step0 raw30767; decide +kernel
      have hl : raw30767step0Labels = raw30767Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30767 raw30767Labels permutation346 hz
    mixedMoment B raw30767step0 raw30767step0Labels = mixedMoment B raw30767step1 raw30767step1Labels := by
      have hz : ∀ i, raw30767step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw30767step1 = (fun i j => raw30767step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw30767step1 raw30767step0; decide +kernel
      have hl : raw30767step1Labels = (fun j => raw30767step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw30767step0 raw30767step0Labels permutation4 hz
    mixedMoment B raw30767step1 raw30767step1Labels = mixedMoment B raw30767step2 raw30767step2Labels := by
      have ha : raw30767step2 = (fun i j => raw30767step1 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw30767step2 raw30767step1; decide +kernel
      have hl : raw30767step2Labels = raw30767step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30767step1 raw30767step1Labels permutation125 permutation0
    mixedMoment B raw30767step2 raw30767step2Labels = mixedMoment B raw30767step3 raw30767step3Labels := by
      have ha : raw30767step3 = -raw30767step2 := by apply Matrix.ext; change ∀ i j, raw30767step3 i j = -(raw30767step2 i j); unfold raw30767step3 raw30767step2; decide +kernel
      have hl : raw30767step3Labels = raw30767step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30767step3 raw30767step3Labels = mixedMoment B raw30767step4 raw30767step4Labels := by
      have ha : raw30767step4 = raw30767step3 := by apply Matrix.ext; unfold raw30767step4 raw30767step3; decide +kernel
      have hl : raw30767step3Labels = labelEmbedding2 ∘ raw30767step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30767step3 raw30767step3Labels raw30767step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw30768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30768Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30768step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30768step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30768step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30768 raw30768Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw30768 raw30768Labels = mixedMoment B raw30768step0 raw30768step0Labels := by
      have hz : ∀ j, raw30768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30768step0 = (fun i j => raw30768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30768step0 raw30768; decide +kernel
      have hl : raw30768step0Labels = raw30768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30768 raw30768Labels permutation346 hz
    mixedMoment B raw30768step0 raw30768step0Labels = mixedMoment B raw30768step1 raw30768step1Labels := by
      have ha : raw30768step1 = (fun i j => raw30768step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30768step1 raw30768step0; decide +kernel
      have hl : raw30768step1Labels = raw30768step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30768step0 raw30768step0Labels permutation151 permutation7
    mixedMoment B raw30768step1 raw30768step1Labels = mixedMoment B raw30768step2 raw30768step2Labels := by
      have ha : raw30768step2 = raw30768step1 := by apply Matrix.ext; unfold raw30768step2 raw30768step1; decide +kernel
      have hl : raw30768step1Labels = labelEmbedding10 ∘ raw30768step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30768step1 raw30768step1Labels raw30768step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw30769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30769Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30769step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30769step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30769step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30769 raw30769Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw30769 raw30769Labels = mixedMoment B raw30769step0 raw30769step0Labels := by
      have hz : ∀ j, raw30769 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30769step0 = (fun i j => raw30769 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30769step0 raw30769; decide +kernel
      have hl : raw30769step0Labels = raw30769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30769 raw30769Labels permutation346 hz
    mixedMoment B raw30769step0 raw30769step0Labels = mixedMoment B raw30769step1 raw30769step1Labels := by
      have ha : raw30769step1 = (fun i j => raw30769step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30769step1 raw30769step0; decide +kernel
      have hl : raw30769step1Labels = raw30769step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30769step0 raw30769step0Labels permutation127 permutation7
    mixedMoment B raw30769step1 raw30769step1Labels = mixedMoment B raw30769step2 raw30769step2Labels := by
      have ha : raw30769step2 = raw30769step1 := by apply Matrix.ext; unfold raw30769step2 raw30769step1; decide +kernel
      have hl : raw30769step1Labels = labelEmbedding10 ∘ raw30769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30769step1 raw30769step1Labels raw30769step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw30770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30770Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30770step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30770 raw30770Labels = mixedMoment B node4586 node4586Labels := by
  calc
    mixedMoment B raw30770 raw30770Labels = mixedMoment B raw30770step0 raw30770step0Labels := by
      have hz : ∀ j, raw30770 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30770step0 = (fun i j => raw30770 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30770step0 raw30770; decide +kernel
      have hl : raw30770step0Labels = raw30770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30770 raw30770Labels permutation346 hz
    _ = mixedMoment B node4586 node4586Labels := by rfl

def raw30771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30771Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30771step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30771step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30771 raw30771Labels = mixedMoment B node5126 node5126Labels := by
  calc
    mixedMoment B raw30771 raw30771Labels = mixedMoment B raw30771step0 raw30771step0Labels := by
      have ha : raw30771step0 = (fun i j => raw30771 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30771step0 raw30771; decide +kernel
      have hl : raw30771step0Labels = raw30771Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30771 raw30771Labels permutation176 permutation2
    _ = mixedMoment B node5126 node5126Labels := by rfl

def raw30772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30772Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30772step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30772step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30772step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30772step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30772 raw30772Labels = mixedMoment B node5063 node5063Labels := by
  calc
    mixedMoment B raw30772 raw30772Labels = mixedMoment B raw30772step0 raw30772step0Labels := by
      have hz : ∀ j, raw30772 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30772step0 = (fun i j => raw30772 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30772step0 raw30772; decide +kernel
      have hl : raw30772step0Labels = raw30772Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30772 raw30772Labels permutation346 hz
    mixedMoment B raw30772step0 raw30772step0Labels = mixedMoment B raw30772step1 raw30772step1Labels := by
      have ha : raw30772step1 = (fun i j => raw30772step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30772step1 raw30772step0; decide +kernel
      have hl : raw30772step1Labels = raw30772step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30772step0 raw30772step0Labels permutation38 permutation2
    _ = mixedMoment B node5063 node5063Labels := by rfl

def raw30773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30773Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30773step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30773step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30773 raw30773Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw30773 raw30773Labels = mixedMoment B raw30773step0 raw30773step0Labels := by
      have hz : ∀ j, raw30773 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30773step0 = (fun i j => raw30773 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30773step0 raw30773; decide +kernel
      have hl : raw30773step0Labels = raw30773Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30773 raw30773Labels permutation346 hz
    _ = mixedMoment B node5248 node5248Labels := by rfl

def raw30774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30774Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30774step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30774step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30774step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30774step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30774 raw30774Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw30774 raw30774Labels = mixedMoment B raw30774step0 raw30774step0Labels := by
      have hz : ∀ j, raw30774 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30774step0 = (fun i j => raw30774 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30774step0 raw30774; decide +kernel
      have hl : raw30774step0Labels = raw30774Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30774 raw30774Labels permutation346 hz
    mixedMoment B raw30774step0 raw30774step0Labels = mixedMoment B raw30774step1 raw30774step1Labels := by
      have ha : raw30774step1 = (fun i j => raw30774step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30774step1 raw30774step0; decide +kernel
      have hl : raw30774step1Labels = raw30774step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30774step0 raw30774step0Labels permutation33 permutation2
    _ = mixedMoment B node5248 node5248Labels := by rfl

def raw30775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30775Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30775step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30775 raw30775Labels = mixedMoment B node4522 node4522Labels := by
  calc
    mixedMoment B raw30775 raw30775Labels = mixedMoment B raw30775step0 raw30775step0Labels := by
      have ha : raw30775step0 = (fun i j => raw30775 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30775step0 raw30775; decide +kernel
      have hl : raw30775step0Labels = raw30775Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30775 raw30775Labels permutation158 permutation2
    _ = mixedMoment B node4522 node4522Labels := by rfl

def raw30776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30776Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30776step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30776step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30776 raw30776Labels = mixedMoment B node4926 node4926Labels := by
  calc
    mixedMoment B raw30776 raw30776Labels = mixedMoment B raw30776step0 raw30776step0Labels := by
      have ha : raw30776step0 = (fun i j => raw30776 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30776step0 raw30776; decide +kernel
      have hl : raw30776step0Labels = raw30776Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30776 raw30776Labels permutation158 permutation2
    _ = mixedMoment B node4926 node4926Labels := by rfl

def raw30777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30777Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30777step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30777step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30777 raw30777Labels = mixedMoment B node5025 node5025Labels := by
  calc
    mixedMoment B raw30777 raw30777Labels = mixedMoment B raw30777step0 raw30777step0Labels := by
      have ha : raw30777step0 = (fun i j => raw30777 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30777step0 raw30777; decide +kernel
      have hl : raw30777step0Labels = raw30777Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30777 raw30777Labels permutation158 permutation2
    _ = mixedMoment B node5025 node5025Labels := by rfl

def raw30778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30778Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30778step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30778step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30778 raw30778Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw30778 raw30778Labels = mixedMoment B raw30778step0 raw30778step0Labels := by
      have ha : raw30778step0 = (fun i j => raw30778 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30778step0 raw30778; decide +kernel
      have hl : raw30778step0Labels = raw30778Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30778 raw30778Labels permutation158 permutation2
    _ = mixedMoment B node5056 node5056Labels := by rfl

def raw30779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30779Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30779step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30779step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30779 raw30779Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw30779 raw30779Labels = mixedMoment B raw30779step0 raw30779step0Labels := by
      have ha : raw30779step0 = (fun i j => raw30779 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30779step0 raw30779; decide +kernel
      have hl : raw30779step0Labels = raw30779Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30779 raw30779Labels permutation159 permutation2
    _ = mixedMoment B node5056 node5056Labels := by rfl

def raw30780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30780Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30780step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30780 raw30780Labels = mixedMoment B node4539 node4539Labels := by
  calc
    mixedMoment B raw30780 raw30780Labels = mixedMoment B raw30780step0 raw30780step0Labels := by
      have hz : ∀ j, raw30780 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30780step0 = (fun i j => raw30780 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30780step0 raw30780; decide +kernel
      have hl : raw30780step0Labels = raw30780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30780 raw30780Labels permutation346 hz
    _ = mixedMoment B node4539 node4539Labels := by rfl

def raw30781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30781Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30781step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30781step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30781 raw30781Labels = mixedMoment B node4937 node4937Labels := by
  calc
    mixedMoment B raw30781 raw30781Labels = mixedMoment B raw30781step0 raw30781step0Labels := by
      have hz : ∀ j, raw30781 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30781step0 = (fun i j => raw30781 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30781step0 raw30781; decide +kernel
      have hl : raw30781step0Labels = raw30781Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30781 raw30781Labels permutation346 hz
    _ = mixedMoment B node4937 node4937Labels := by rfl

def raw30782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30782Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30782 raw30782Labels = mixedMoment B node5032 node5032Labels := by
  calc
    _ = mixedMoment B node5032 node5032Labels := by rfl

def raw30783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30783Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30783step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30783 raw30783Labels = mixedMoment B node5095 node5095Labels := by
  calc
    mixedMoment B raw30783 raw30783Labels = mixedMoment B raw30783step0 raw30783step0Labels := by
      have hz : ∀ j, raw30783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30783step0 = (fun i j => raw30783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30783step0 raw30783; decide +kernel
      have hl : raw30783step0Labels = raw30783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30783 raw30783Labels permutation346 hz
    _ = mixedMoment B node5095 node5095Labels := by rfl

def raw30784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30784Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30784step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30784step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30784 raw30784Labels = mixedMoment B node5095 node5095Labels := by
  calc
    mixedMoment B raw30784 raw30784Labels = mixedMoment B raw30784step0 raw30784step0Labels := by
      have hz : ∀ j, raw30784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30784step0 = (fun i j => raw30784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30784step0 raw30784; decide +kernel
      have hl : raw30784step0Labels = raw30784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30784 raw30784Labels permutation346 hz
    mixedMoment B raw30784step0 raw30784step0Labels = mixedMoment B raw30784step1 raw30784step1Labels := by
      have ha : raw30784step1 = (fun i j => raw30784step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30784step1 raw30784step0; decide +kernel
      have hl : raw30784step1Labels = raw30784step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30784step0 raw30784step0Labels permutation33 permutation2
    _ = mixedMoment B node5095 node5095Labels := by rfl

def raw30785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30785Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30785step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30785step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30785step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30785step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30785 raw30785Labels = mixedMoment B node4526 node4526Labels := by
  calc
    mixedMoment B raw30785 raw30785Labels = mixedMoment B raw30785step0 raw30785step0Labels := by
      have hz : ∀ j, raw30785 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30785step0 = (fun i j => raw30785 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30785step0 raw30785; decide +kernel
      have hl : raw30785step0Labels = raw30785Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30785 raw30785Labels permutation346 hz
    mixedMoment B raw30785step0 raw30785step0Labels = mixedMoment B raw30785step1 raw30785step1Labels := by
      have ha : raw30785step1 = (fun i j => raw30785step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30785step1 raw30785step0; decide +kernel
      have hl : raw30785step1Labels = raw30785step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30785step0 raw30785step0Labels permutation33 permutation2
    _ = mixedMoment B node4526 node4526Labels := by rfl

def raw30786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30786Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30786step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw30786step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30786step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30786step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30786 raw30786Labels = mixedMoment B node4907 node4907Labels := by
  calc
    mixedMoment B raw30786 raw30786Labels = mixedMoment B raw30786step0 raw30786step0Labels := by
      have hz : ∀ j, raw30786 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30786step0 = (fun i j => raw30786 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30786step0 raw30786; decide +kernel
      have hl : raw30786step0Labels = raw30786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30786 raw30786Labels permutation346 hz
    mixedMoment B raw30786step0 raw30786step0Labels = mixedMoment B raw30786step1 raw30786step1Labels := by
      have ha : raw30786step1 = (fun i j => raw30786step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30786step1 raw30786step0; decide +kernel
      have hl : raw30786step1Labels = raw30786step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30786step0 raw30786step0Labels permutation127 permutation2
    mixedMoment B raw30786step1 raw30786step1Labels = mixedMoment B raw30786step2 raw30786step2Labels := by
      have ha : raw30786step2 = -raw30786step1 := by apply Matrix.ext; change ∀ i j, raw30786step2 i j = -(raw30786step1 i j); unfold raw30786step2 raw30786step1; decide +kernel
      have hl : raw30786step2Labels = raw30786step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4907 node4907Labels := by rfl

def raw30787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30787Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30787step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30787step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30787step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30787step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30787 raw30787Labels = mixedMoment B node4902 node4902Labels := by
  calc
    mixedMoment B raw30787 raw30787Labels = mixedMoment B raw30787step0 raw30787step0Labels := by
      have ha : raw30787step0 = (fun i j => raw30787 (permutation589 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30787step0 raw30787; decide +kernel
      have hl : raw30787step0Labels = raw30787Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30787 raw30787Labels permutation589 permutation2
    mixedMoment B raw30787step0 raw30787step0Labels = mixedMoment B raw30787step1 raw30787step1Labels := by
      have ha : raw30787step1 = -raw30787step0 := by apply Matrix.ext; change ∀ i j, raw30787step1 i j = -(raw30787step0 i j); unfold raw30787step1 raw30787step0; decide +kernel
      have hl : raw30787step1Labels = raw30787step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4902 node4902Labels := by rfl

def raw30788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30788Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30788step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30788step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30788step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw30788step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30788 raw30788Labels = mixedMoment B node4918 node4918Labels := by
  calc
    mixedMoment B raw30788 raw30788Labels = mixedMoment B raw30788step0 raw30788step0Labels := by
      have hz : ∀ j, raw30788 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30788step0 = (fun i j => raw30788 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30788step0 raw30788; decide +kernel
      have hl : raw30788step0Labels = raw30788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30788 raw30788Labels permutation346 hz
    mixedMoment B raw30788step0 raw30788step0Labels = mixedMoment B raw30788step1 raw30788step1Labels := by
      have ha : raw30788step1 = (fun i j => raw30788step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30788step1 raw30788step0; decide +kernel
      have hl : raw30788step1Labels = raw30788step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30788step0 raw30788step0Labels permutation125 permutation2
    mixedMoment B raw30788step1 raw30788step1Labels = mixedMoment B raw30788step2 raw30788step2Labels := by
      have ha : raw30788step2 = -raw30788step1 := by apply Matrix.ext; change ∀ i j, raw30788step2 i j = -(raw30788step1 i j); unfold raw30788step2 raw30788step1; decide +kernel
      have hl : raw30788step2Labels = raw30788step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4918 node4918Labels := by rfl

def raw30789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw30789Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30789step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw30789step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30789step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30789step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30789step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw30789step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30789 raw30789Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw30789 raw30789Labels = mixedMoment B raw30789step0 raw30789step0Labels := by
      have hz : ∀ j, raw30789 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30789step0 = (fun i j => raw30789 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30789step0 raw30789; decide +kernel
      have hl : raw30789step0Labels = raw30789Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30789 raw30789Labels permutation346 hz
    mixedMoment B raw30789step0 raw30789step0Labels = mixedMoment B raw30789step1 raw30789step1Labels := by
      have ha : raw30789step1 = (fun i j => raw30789step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30789step1 raw30789step0; decide +kernel
      have hl : raw30789step1Labels = raw30789step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30789step0 raw30789step0Labels permutation127 permutation2
    mixedMoment B raw30789step1 raw30789step1Labels = mixedMoment B raw30789step2 raw30789step2Labels := by
      have ha : raw30789step2 = -raw30789step1 := by apply Matrix.ext; change ∀ i j, raw30789step2 i j = -(raw30789step1 i j); unfold raw30789step2 raw30789step1; decide +kernel
      have hl : raw30789step2Labels = raw30789step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5000 node5000Labels := by rfl

def raw30790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30790Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30790step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30790 raw30790Labels = mixedMoment B node4526 node4526Labels := by
  calc
    mixedMoment B raw30790 raw30790Labels = mixedMoment B raw30790step0 raw30790step0Labels := by
      have hz : ∀ j, raw30790 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30790step0 = (fun i j => raw30790 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30790step0 raw30790; decide +kernel
      have hl : raw30790step0Labels = raw30790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30790 raw30790Labels permutation346 hz
    _ = mixedMoment B node4526 node4526Labels := by rfl

def raw30791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw30791step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30791step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![3, -1, -2]]
def raw30791step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30791 raw30791Labels = mixedMoment B node4907 node4907Labels := by
  calc
    mixedMoment B raw30791 raw30791Labels = mixedMoment B raw30791step0 raw30791step0Labels := by
      have hz : ∀ j, raw30791 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30791step0 = (fun i j => raw30791 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30791step0 raw30791; decide +kernel
      have hl : raw30791step0Labels = raw30791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30791 raw30791Labels permutation346 hz
    mixedMoment B raw30791step0 raw30791step0Labels = mixedMoment B raw30791step1 raw30791step1Labels := by
      have ha : raw30791step1 = (fun i j => raw30791step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30791step1 raw30791step0; decide +kernel
      have hl : raw30791step1Labels = raw30791step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30791step0 raw30791step0Labels permutation151 permutation2
    mixedMoment B raw30791step1 raw30791step1Labels = mixedMoment B raw30791step2 raw30791step2Labels := by
      have ha : raw30791step2 = -raw30791step1 := by apply Matrix.ext; change ∀ i j, raw30791step2 i j = -(raw30791step1 i j); unfold raw30791step2 raw30791step1; decide +kernel
      have hl : raw30791step2Labels = raw30791step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4907 node4907Labels := by rfl

def raw30792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30792step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30792step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30792 raw30792Labels = mixedMoment B node4902 node4902Labels := by
  calc
    mixedMoment B raw30792 raw30792Labels = mixedMoment B raw30792step0 raw30792step0Labels := by
      have ha : raw30792step0 = (fun i j => raw30792 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30792step0 raw30792; decide +kernel
      have hl : raw30792step0Labels = raw30792Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30792 raw30792Labels permutation688 permutation2
    mixedMoment B raw30792step0 raw30792step0Labels = mixedMoment B raw30792step1 raw30792step1Labels := by
      have ha : raw30792step1 = -raw30792step0 := by apply Matrix.ext; change ∀ i j, raw30792step1 i j = -(raw30792step0 i j); unfold raw30792step1 raw30792step0; decide +kernel
      have hl : raw30792step1Labels = raw30792step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4902 node4902Labels := by rfl

def raw30793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30793step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw30793step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30793 raw30793Labels = mixedMoment B node4918 node4918Labels := by
  calc
    mixedMoment B raw30793 raw30793Labels = mixedMoment B raw30793step0 raw30793step0Labels := by
      have hz : ∀ j, raw30793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30793step0 = (fun i j => raw30793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30793step0 raw30793; decide +kernel
      have hl : raw30793step0Labels = raw30793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30793 raw30793Labels permutation346 hz
    mixedMoment B raw30793step0 raw30793step0Labels = mixedMoment B raw30793step1 raw30793step1Labels := by
      have ha : raw30793step1 = (fun i j => raw30793step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30793step1 raw30793step0; decide +kernel
      have hl : raw30793step1Labels = raw30793step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30793step0 raw30793step0Labels permutation149 permutation2
    mixedMoment B raw30793step1 raw30793step1Labels = mixedMoment B raw30793step2 raw30793step2Labels := by
      have ha : raw30793step2 = -raw30793step1 := by apply Matrix.ext; change ∀ i j, raw30793step2 i j = -(raw30793step1 i j); unfold raw30793step2 raw30793step1; decide +kernel
      have hl : raw30793step2Labels = raw30793step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4918 node4918Labels := by rfl

def raw30794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw30794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw30794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30794step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw30794step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30794 raw30794Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw30794 raw30794Labels = mixedMoment B raw30794step0 raw30794step0Labels := by
      have hz : ∀ j, raw30794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30794step0 = (fun i j => raw30794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30794step0 raw30794; decide +kernel
      have hl : raw30794step0Labels = raw30794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30794 raw30794Labels permutation346 hz
    mixedMoment B raw30794step0 raw30794step0Labels = mixedMoment B raw30794step1 raw30794step1Labels := by
      have ha : raw30794step1 = (fun i j => raw30794step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30794step1 raw30794step0; decide +kernel
      have hl : raw30794step1Labels = raw30794step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30794step0 raw30794step0Labels permutation151 permutation2
    mixedMoment B raw30794step1 raw30794step1Labels = mixedMoment B raw30794step2 raw30794step2Labels := by
      have ha : raw30794step2 = -raw30794step1 := by apply Matrix.ext; change ∀ i j, raw30794step2 i j = -(raw30794step1 i j); unfold raw30794step2 raw30794step1; decide +kernel
      have hl : raw30794step2Labels = raw30794step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5000 node5000Labels := by rfl

def raw30795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30795Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30795step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30795step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30795step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30795step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30795step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30795step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30795 raw30795Labels = mixedMoment B node3664 node3664Labels := by
  calc
    mixedMoment B raw30795 raw30795Labels = mixedMoment B raw30795step0 raw30795step0Labels := by
      have hz : ∀ j, raw30795 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30795step0 = (fun i j => raw30795 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30795step0 raw30795; decide +kernel
      have hl : raw30795step0Labels = raw30795Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30795 raw30795Labels permutation346 hz
    mixedMoment B raw30795step0 raw30795step0Labels = mixedMoment B raw30795step1 raw30795step1Labels := by
      have ha : raw30795step1 = (fun i j => raw30795step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30795step1 raw30795step0; decide +kernel
      have hl : raw30795step1Labels = raw30795step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30795step0 raw30795step0Labels permutation127 permutation7
    mixedMoment B raw30795step1 raw30795step1Labels = mixedMoment B raw30795step2 raw30795step2Labels := by
      have ha : raw30795step2 = raw30795step1 := by apply Matrix.ext; unfold raw30795step2 raw30795step1; decide +kernel
      have hl : raw30795step1Labels = labelEmbedding1 ∘ raw30795step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30795step1 raw30795step1Labels raw30795step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3664 node3664Labels := by rfl

def raw30796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30796Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30796step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30796step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30796 raw30796Labels = mixedMoment B node3650 node3650Labels := by
  calc
    mixedMoment B raw30796 raw30796Labels = mixedMoment B raw30796step0 raw30796step0Labels := by
      have ha : raw30796step0 = (fun i j => raw30796 (permutation584 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30796step0 raw30796; decide +kernel
      have hl : raw30796step0Labels = raw30796Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30796 raw30796Labels permutation584 permutation7
    mixedMoment B raw30796step0 raw30796step0Labels = mixedMoment B raw30796step1 raw30796step1Labels := by
      have ha : raw30796step1 = raw30796step0 := by apply Matrix.ext; unfold raw30796step1 raw30796step0; decide +kernel
      have hl : raw30796step0Labels = labelEmbedding1 ∘ raw30796step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30796step0 raw30796step0Labels raw30796step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3650 node3650Labels := by rfl

def raw30797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30797Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30797step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30797step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30797step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw30797step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30797step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw30797step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw30797step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw30797step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical30797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30797 raw30797Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw30797 raw30797Labels = mixedMoment B raw30797step0 raw30797step0Labels := by
      have hz : ∀ j, raw30797 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30797step0 = (fun i j => raw30797 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30797step0 raw30797; decide +kernel
      have hl : raw30797step0Labels = raw30797Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30797 raw30797Labels permutation346 hz
    mixedMoment B raw30797step0 raw30797step0Labels = mixedMoment B raw30797step1 raw30797step1Labels := by
      have hz : ∀ i, raw30797step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw30797step1 = (fun i j => raw30797step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw30797step1 raw30797step0; decide +kernel
      have hl : raw30797step1Labels = (fun j => raw30797step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw30797step0 raw30797step0Labels permutation4 hz
    mixedMoment B raw30797step1 raw30797step1Labels = mixedMoment B raw30797step2 raw30797step2Labels := by
      have ha : raw30797step2 = (fun i j => raw30797step1 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw30797step2 raw30797step1; decide +kernel
      have hl : raw30797step2Labels = raw30797step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30797step1 raw30797step1Labels permutation125 permutation0
    mixedMoment B raw30797step2 raw30797step2Labels = mixedMoment B raw30797step3 raw30797step3Labels := by
      have ha : raw30797step3 = -raw30797step2 := by apply Matrix.ext; change ∀ i j, raw30797step3 i j = -(raw30797step2 i j); unfold raw30797step3 raw30797step2; decide +kernel
      have hl : raw30797step3Labels = raw30797step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw30798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30798Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30798step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30798step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30798step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30798step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30798step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30798step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30798 raw30798Labels = mixedMoment B node3704 node3704Labels := by
  calc
    mixedMoment B raw30798 raw30798Labels = mixedMoment B raw30798step0 raw30798step0Labels := by
      have hz : ∀ j, raw30798 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30798step0 = (fun i j => raw30798 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30798step0 raw30798; decide +kernel
      have hl : raw30798step0Labels = raw30798Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30798 raw30798Labels permutation346 hz
    mixedMoment B raw30798step0 raw30798step0Labels = mixedMoment B raw30798step1 raw30798step1Labels := by
      have ha : raw30798step1 = (fun i j => raw30798step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30798step1 raw30798step0; decide +kernel
      have hl : raw30798step1Labels = raw30798step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30798step0 raw30798step0Labels permutation151 permutation7
    mixedMoment B raw30798step1 raw30798step1Labels = mixedMoment B raw30798step2 raw30798step2Labels := by
      have ha : raw30798step2 = raw30798step1 := by apply Matrix.ext; unfold raw30798step2 raw30798step1; decide +kernel
      have hl : raw30798step1Labels = labelEmbedding1 ∘ raw30798step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30798step1 raw30798step1Labels raw30798step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3704 node3704Labels := by rfl

def raw30799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30799Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30799step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30799step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw30799step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30799 raw30799Labels = mixedMoment B node3704 node3704Labels := by
  calc
    mixedMoment B raw30799 raw30799Labels = mixedMoment B raw30799step0 raw30799step0Labels := by
      have hz : ∀ j, raw30799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30799step0 = (fun i j => raw30799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30799step0 raw30799; decide +kernel
      have hl : raw30799step0Labels = raw30799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30799 raw30799Labels permutation346 hz
    mixedMoment B raw30799step0 raw30799step0Labels = mixedMoment B raw30799step1 raw30799step1Labels := by
      have ha : raw30799step1 = (fun i j => raw30799step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30799step1 raw30799step0; decide +kernel
      have hl : raw30799step1Labels = raw30799step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30799step0 raw30799step0Labels permutation127 permutation7
    mixedMoment B raw30799step1 raw30799step1Labels = mixedMoment B raw30799step2 raw30799step2Labels := by
      have ha : raw30799step2 = raw30799step1 := by apply Matrix.ext; unfold raw30799step2 raw30799step1; decide +kernel
      have hl : raw30799step1Labels = labelEmbedding1 ∘ raw30799step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30799step1 raw30799step1Labels raw30799step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3704 node3704Labels := by rfl

def raw30800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30800Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30800step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30800step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30800step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30800step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30800step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30800 raw30800Labels = mixedMoment B node3284 node3284Labels := by
  calc
    mixedMoment B raw30800 raw30800Labels = mixedMoment B raw30800step0 raw30800step0Labels := by
      have hz : ∀ j, raw30800 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30800step0 = (fun i j => raw30800 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30800step0 raw30800; decide +kernel
      have hl : raw30800step0Labels = raw30800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30800 raw30800Labels permutation346 hz
    mixedMoment B raw30800step0 raw30800step0Labels = mixedMoment B raw30800step1 raw30800step1Labels := by
      have ha : raw30800step1 = (fun i j => raw30800step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30800step1 raw30800step0; decide +kernel
      have hl : raw30800step1Labels = raw30800step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30800step0 raw30800step0Labels permutation32 permutation7
    mixedMoment B raw30800step1 raw30800step1Labels = mixedMoment B raw30800step2 raw30800step2Labels := by
      have ha : raw30800step2 = -raw30800step1 := by apply Matrix.ext; change ∀ i j, raw30800step2 i j = -(raw30800step1 i j); unfold raw30800step2 raw30800step1; decide +kernel
      have hl : raw30800step2Labels = raw30800step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30800step2 raw30800step2Labels = mixedMoment B raw30800step3 raw30800step3Labels := by
      have ha : raw30800step3 = raw30800step2 := by apply Matrix.ext; unfold raw30800step3 raw30800step2; decide +kernel
      have hl : raw30800step2Labels = labelEmbedding1 ∘ raw30800step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30800step2 raw30800step2Labels raw30800step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3284 node3284Labels := by rfl

def raw30801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30801Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw30801step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30801step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30801step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30801step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30801 raw30801Labels = mixedMoment B node3487 node3487Labels := by
  calc
    mixedMoment B raw30801 raw30801Labels = mixedMoment B raw30801step0 raw30801step0Labels := by
      have ha : raw30801step0 = (fun i j => raw30801 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30801step0 raw30801; decide +kernel
      have hl : raw30801step0Labels = raw30801Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30801 raw30801Labels permutation158 permutation7
    mixedMoment B raw30801step0 raw30801step0Labels = mixedMoment B raw30801step1 raw30801step1Labels := by
      have ha : raw30801step1 = -raw30801step0 := by apply Matrix.ext; change ∀ i j, raw30801step1 i j = -(raw30801step0 i j); unfold raw30801step1 raw30801step0; decide +kernel
      have hl : raw30801step1Labels = raw30801step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30801step1 raw30801step1Labels = mixedMoment B raw30801step2 raw30801step2Labels := by
      have ha : raw30801step2 = raw30801step1 := by apply Matrix.ext; unfold raw30801step2 raw30801step1; decide +kernel
      have hl : raw30801step1Labels = labelEmbedding1 ∘ raw30801step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30801step1 raw30801step1Labels raw30801step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3487 node3487Labels := by rfl

def raw30802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30802Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30802step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30802step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30802step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30802step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30802step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30802 raw30802Labels = mixedMoment B node3439 node3439Labels := by
  calc
    mixedMoment B raw30802 raw30802Labels = mixedMoment B raw30802step0 raw30802step0Labels := by
      have hz : ∀ j, raw30802 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30802step0 = (fun i j => raw30802 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30802step0 raw30802; decide +kernel
      have hl : raw30802step0Labels = raw30802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30802 raw30802Labels permutation346 hz
    mixedMoment B raw30802step0 raw30802step0Labels = mixedMoment B raw30802step1 raw30802step1Labels := by
      have ha : raw30802step1 = (fun i j => raw30802step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30802step1 raw30802step0; decide +kernel
      have hl : raw30802step1Labels = raw30802step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30802step0 raw30802step0Labels permutation38 permutation7
    mixedMoment B raw30802step1 raw30802step1Labels = mixedMoment B raw30802step2 raw30802step2Labels := by
      have ha : raw30802step2 = -raw30802step1 := by apply Matrix.ext; change ∀ i j, raw30802step2 i j = -(raw30802step1 i j); unfold raw30802step2 raw30802step1; decide +kernel
      have hl : raw30802step2Labels = raw30802step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30802step2 raw30802step2Labels = mixedMoment B raw30802step3 raw30802step3Labels := by
      have ha : raw30802step3 = raw30802step2 := by apply Matrix.ext; unfold raw30802step3 raw30802step2; decide +kernel
      have hl : raw30802step2Labels = labelEmbedding1 ∘ raw30802step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30802step2 raw30802step2Labels raw30802step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3439 node3439Labels := by rfl

def raw30803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30803Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30803step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw30803step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30803step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30803step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30803step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30803step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30803 raw30803Labels = mixedMoment B node3498 node3498Labels := by
  calc
    mixedMoment B raw30803 raw30803Labels = mixedMoment B raw30803step0 raw30803step0Labels := by
      have hz : ∀ j, raw30803 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30803step0 = (fun i j => raw30803 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30803step0 raw30803; decide +kernel
      have hl : raw30803step0Labels = raw30803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30803 raw30803Labels permutation346 hz
    mixedMoment B raw30803step0 raw30803step0Labels = mixedMoment B raw30803step1 raw30803step1Labels := by
      have ha : raw30803step1 = (fun i j => raw30803step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30803step1 raw30803step0; decide +kernel
      have hl : raw30803step1Labels = raw30803step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30803step0 raw30803step0Labels permutation32 permutation7
    mixedMoment B raw30803step1 raw30803step1Labels = mixedMoment B raw30803step2 raw30803step2Labels := by
      have ha : raw30803step2 = -raw30803step1 := by apply Matrix.ext; change ∀ i j, raw30803step2 i j = -(raw30803step1 i j); unfold raw30803step2 raw30803step1; decide +kernel
      have hl : raw30803step2Labels = raw30803step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30803step2 raw30803step2Labels = mixedMoment B raw30803step3 raw30803step3Labels := by
      have ha : raw30803step3 = raw30803step2 := by apply Matrix.ext; unfold raw30803step3 raw30803step2; decide +kernel
      have hl : raw30803step2Labels = labelEmbedding1 ∘ raw30803step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30803step2 raw30803step2Labels raw30803step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3498 node3498Labels := by rfl

def raw30804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30804Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30804step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw30804step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30804step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30804step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30804step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw30804step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30804 raw30804Labels = mixedMoment B node3498 node3498Labels := by
  calc
    mixedMoment B raw30804 raw30804Labels = mixedMoment B raw30804step0 raw30804step0Labels := by
      have hz : ∀ j, raw30804 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30804step0 = (fun i j => raw30804 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30804step0 raw30804; decide +kernel
      have hl : raw30804step0Labels = raw30804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30804 raw30804Labels permutation346 hz
    mixedMoment B raw30804step0 raw30804step0Labels = mixedMoment B raw30804step1 raw30804step1Labels := by
      have ha : raw30804step1 = (fun i j => raw30804step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30804step1 raw30804step0; decide +kernel
      have hl : raw30804step1Labels = raw30804step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30804step0 raw30804step0Labels permutation33 permutation7
    mixedMoment B raw30804step1 raw30804step1Labels = mixedMoment B raw30804step2 raw30804step2Labels := by
      have ha : raw30804step2 = -raw30804step1 := by apply Matrix.ext; change ∀ i j, raw30804step2 i j = -(raw30804step1 i j); unfold raw30804step2 raw30804step1; decide +kernel
      have hl : raw30804step2Labels = raw30804step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30804step2 raw30804step2Labels = mixedMoment B raw30804step3 raw30804step3Labels := by
      have ha : raw30804step3 = raw30804step2 := by apply Matrix.ext; unfold raw30804step3 raw30804step2; decide +kernel
      have hl : raw30804step2Labels = labelEmbedding1 ∘ raw30804step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30804step2 raw30804step2Labels raw30804step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3498 node3498Labels := by rfl

def raw30805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30805Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw30805step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30805step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw30805step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30805step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw30805step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30805 raw30805Labels = mixedMoment B node3249 node3249Labels := by
  calc
    mixedMoment B raw30805 raw30805Labels = mixedMoment B raw30805step0 raw30805step0Labels := by
      have ha : raw30805step0 = (fun i j => raw30805 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30805step0 raw30805; decide +kernel
      have hl : raw30805step0Labels = raw30805Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30805 raw30805Labels permutation158 permutation7
    mixedMoment B raw30805step0 raw30805step0Labels = mixedMoment B raw30805step1 raw30805step1Labels := by
      have ha : raw30805step1 = -raw30805step0 := by apply Matrix.ext; change ∀ i j, raw30805step1 i j = -(raw30805step0 i j); unfold raw30805step1 raw30805step0; decide +kernel
      have hl : raw30805step1Labels = raw30805step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30805step1 raw30805step1Labels = mixedMoment B raw30805step2 raw30805step2Labels := by
      have ha : raw30805step2 = raw30805step1 := by apply Matrix.ext; unfold raw30805step2 raw30805step1; decide +kernel
      have hl : raw30805step1Labels = labelEmbedding1 ∘ raw30805step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30805step1 raw30805step1Labels raw30805step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3249 node3249Labels := by rfl

def raw30806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30806Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30806step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw30806step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30806step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw30806step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30806step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw30806step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30806 raw30806Labels = mixedMoment B node3398 node3398Labels := by
  calc
    mixedMoment B raw30806 raw30806Labels = mixedMoment B raw30806step0 raw30806step0Labels := by
      have ha : raw30806step0 = (fun i j => raw30806 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30806step0 raw30806; decide +kernel
      have hl : raw30806step0Labels = raw30806Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30806 raw30806Labels permutation158 permutation7
    mixedMoment B raw30806step0 raw30806step0Labels = mixedMoment B raw30806step1 raw30806step1Labels := by
      have ha : raw30806step1 = -raw30806step0 := by apply Matrix.ext; change ∀ i j, raw30806step1 i j = -(raw30806step0 i j); unfold raw30806step1 raw30806step0; decide +kernel
      have hl : raw30806step1Labels = raw30806step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30806step1 raw30806step1Labels = mixedMoment B raw30806step2 raw30806step2Labels := by
      have ha : raw30806step2 = raw30806step1 := by apply Matrix.ext; unfold raw30806step2 raw30806step1; decide +kernel
      have hl : raw30806step1Labels = labelEmbedding1 ∘ raw30806step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30806step1 raw30806step1Labels raw30806step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3398 node3398Labels := by rfl

def raw30807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30807Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30807step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw30807step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30807step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw30807step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30807step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw30807step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30807 raw30807Labels = mixedMoment B node3424 node3424Labels := by
  calc
    mixedMoment B raw30807 raw30807Labels = mixedMoment B raw30807step0 raw30807step0Labels := by
      have ha : raw30807step0 = (fun i j => raw30807 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30807step0 raw30807; decide +kernel
      have hl : raw30807step0Labels = raw30807Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30807 raw30807Labels permutation158 permutation7
    mixedMoment B raw30807step0 raw30807step0Labels = mixedMoment B raw30807step1 raw30807step1Labels := by
      have ha : raw30807step1 = -raw30807step0 := by apply Matrix.ext; change ∀ i j, raw30807step1 i j = -(raw30807step0 i j); unfold raw30807step1 raw30807step0; decide +kernel
      have hl : raw30807step1Labels = raw30807step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30807step1 raw30807step1Labels = mixedMoment B raw30807step2 raw30807step2Labels := by
      have ha : raw30807step2 = raw30807step1 := by apply Matrix.ext; unfold raw30807step2 raw30807step1; decide +kernel
      have hl : raw30807step1Labels = labelEmbedding1 ∘ raw30807step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30807step1 raw30807step1Labels raw30807step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3424 node3424Labels := by rfl

def raw30808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30808Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw30808step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30808step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30808step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30808step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30808step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30808 raw30808Labels = mixedMoment B node3429 node3429Labels := by
  calc
    mixedMoment B raw30808 raw30808Labels = mixedMoment B raw30808step0 raw30808step0Labels := by
      have ha : raw30808step0 = (fun i j => raw30808 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30808step0 raw30808; decide +kernel
      have hl : raw30808step0Labels = raw30808Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30808 raw30808Labels permutation158 permutation7
    mixedMoment B raw30808step0 raw30808step0Labels = mixedMoment B raw30808step1 raw30808step1Labels := by
      have ha : raw30808step1 = -raw30808step0 := by apply Matrix.ext; change ∀ i j, raw30808step1 i j = -(raw30808step0 i j); unfold raw30808step1 raw30808step0; decide +kernel
      have hl : raw30808step1Labels = raw30808step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30808step1 raw30808step1Labels = mixedMoment B raw30808step2 raw30808step2Labels := by
      have ha : raw30808step2 = raw30808step1 := by apply Matrix.ext; unfold raw30808step2 raw30808step1; decide +kernel
      have hl : raw30808step1Labels = labelEmbedding1 ∘ raw30808step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30808step1 raw30808step1Labels raw30808step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3429 node3429Labels := by rfl

def raw30809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30809Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw30809step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30809step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30809step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30809step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30809step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30809 raw30809Labels = mixedMoment B node3429 node3429Labels := by
  calc
    mixedMoment B raw30809 raw30809Labels = mixedMoment B raw30809step0 raw30809step0Labels := by
      have ha : raw30809step0 = (fun i j => raw30809 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30809step0 raw30809; decide +kernel
      have hl : raw30809step0Labels = raw30809Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30809 raw30809Labels permutation159 permutation7
    mixedMoment B raw30809step0 raw30809step0Labels = mixedMoment B raw30809step1 raw30809step1Labels := by
      have ha : raw30809step1 = -raw30809step0 := by apply Matrix.ext; change ∀ i j, raw30809step1 i j = -(raw30809step0 i j); unfold raw30809step1 raw30809step0; decide +kernel
      have hl : raw30809step1Labels = raw30809step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30809step1 raw30809step1Labels = mixedMoment B raw30809step2 raw30809step2Labels := by
      have ha : raw30809step2 = raw30809step1 := by apply Matrix.ext; unfold raw30809step2 raw30809step1; decide +kernel
      have hl : raw30809step1Labels = labelEmbedding1 ∘ raw30809step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30809step1 raw30809step1Labels raw30809step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3429 node3429Labels := by rfl

def raw30810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30810Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30810step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30810step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30810step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -2, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw30810step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30810step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw30810step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30810step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw30810step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30810 raw30810Labels = mixedMoment B node3254 node3254Labels := by
  calc
    mixedMoment B raw30810 raw30810Labels = mixedMoment B raw30810step0 raw30810step0Labels := by
      have hz : ∀ j, raw30810 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30810step0 = (fun i j => raw30810 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30810step0 raw30810; decide +kernel
      have hl : raw30810step0Labels = raw30810Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30810 raw30810Labels permutation346 hz
    mixedMoment B raw30810step0 raw30810step0Labels = mixedMoment B raw30810step1 raw30810step1Labels := by
      have ha : raw30810step1 = (fun i j => raw30810step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30810step1 raw30810step0; decide +kernel
      have hl : raw30810step1Labels = raw30810step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30810step0 raw30810step0Labels permutation32 permutation7
    mixedMoment B raw30810step1 raw30810step1Labels = mixedMoment B raw30810step2 raw30810step2Labels := by
      have ha : raw30810step2 = -raw30810step1 := by apply Matrix.ext; change ∀ i j, raw30810step2 i j = -(raw30810step1 i j); unfold raw30810step2 raw30810step1; decide +kernel
      have hl : raw30810step2Labels = raw30810step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30810step2 raw30810step2Labels = mixedMoment B raw30810step3 raw30810step3Labels := by
      have ha : raw30810step3 = raw30810step2 := by apply Matrix.ext; unfold raw30810step3 raw30810step2; decide +kernel
      have hl : raw30810step2Labels = labelEmbedding1 ∘ raw30810step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30810step2 raw30810step2Labels raw30810step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3254 node3254Labels := by rfl

def raw30811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30811Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30811step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30811step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30811step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![1, -2, 1], ![-2, 0, 2], ![-2, 0, 2]]
def raw30811step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30811step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw30811step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30811step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![-1, 2, -1], ![2, 0, -2], ![2, 0, -2]]
def raw30811step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30811 raw30811Labels = mixedMoment B node3402 node3402Labels := by
  calc
    mixedMoment B raw30811 raw30811Labels = mixedMoment B raw30811step0 raw30811step0Labels := by
      have hz : ∀ j, raw30811 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30811step0 = (fun i j => raw30811 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30811step0 raw30811; decide +kernel
      have hl : raw30811step0Labels = raw30811Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30811 raw30811Labels permutation346 hz
    mixedMoment B raw30811step0 raw30811step0Labels = mixedMoment B raw30811step1 raw30811step1Labels := by
      have ha : raw30811step1 = (fun i j => raw30811step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30811step1 raw30811step0; decide +kernel
      have hl : raw30811step1Labels = raw30811step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30811step0 raw30811step0Labels permutation32 permutation7
    mixedMoment B raw30811step1 raw30811step1Labels = mixedMoment B raw30811step2 raw30811step2Labels := by
      have ha : raw30811step2 = -raw30811step1 := by apply Matrix.ext; change ∀ i j, raw30811step2 i j = -(raw30811step1 i j); unfold raw30811step2 raw30811step1; decide +kernel
      have hl : raw30811step2Labels = raw30811step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30811step2 raw30811step2Labels = mixedMoment B raw30811step3 raw30811step3Labels := by
      have ha : raw30811step3 = raw30811step2 := by apply Matrix.ext; unfold raw30811step3 raw30811step2; decide +kernel
      have hl : raw30811step2Labels = labelEmbedding1 ∘ raw30811step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30811step2 raw30811step2Labels raw30811step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3402 node3402Labels := by rfl

def raw30812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30812Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30812step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw30812step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30812step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30812step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30812step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30812step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30812 raw30812Labels = mixedMoment B node3440 node3440Labels := by
  calc
    mixedMoment B raw30812 raw30812Labels = mixedMoment B raw30812step0 raw30812step0Labels := by
      have ha : raw30812step0 = (fun i j => raw30812 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30812step0 raw30812; decide +kernel
      have hl : raw30812step0Labels = raw30812Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30812 raw30812Labels permutation158 permutation7
    mixedMoment B raw30812step0 raw30812step0Labels = mixedMoment B raw30812step1 raw30812step1Labels := by
      have ha : raw30812step1 = -raw30812step0 := by apply Matrix.ext; change ∀ i j, raw30812step1 i j = -(raw30812step0 i j); unfold raw30812step1 raw30812step0; decide +kernel
      have hl : raw30812step1Labels = raw30812step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30812step1 raw30812step1Labels = mixedMoment B raw30812step2 raw30812step2Labels := by
      have ha : raw30812step2 = raw30812step1 := by apply Matrix.ext; unfold raw30812step2 raw30812step1; decide +kernel
      have hl : raw30812step1Labels = labelEmbedding1 ∘ raw30812step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30812step1 raw30812step1Labels raw30812step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3440 node3440Labels := by rfl

def raw30813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30813Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30813step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw30813step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30813step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30813step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30813step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30813step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30813 raw30813Labels = mixedMoment B node3448 node3448Labels := by
  calc
    mixedMoment B raw30813 raw30813Labels = mixedMoment B raw30813step0 raw30813step0Labels := by
      have hz : ∀ j, raw30813 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30813step0 = (fun i j => raw30813 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30813step0 raw30813; decide +kernel
      have hl : raw30813step0Labels = raw30813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30813 raw30813Labels permutation346 hz
    mixedMoment B raw30813step0 raw30813step0Labels = mixedMoment B raw30813step1 raw30813step1Labels := by
      have ha : raw30813step1 = (fun i j => raw30813step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30813step1 raw30813step0; decide +kernel
      have hl : raw30813step1Labels = raw30813step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30813step0 raw30813step0Labels permutation32 permutation7
    mixedMoment B raw30813step1 raw30813step1Labels = mixedMoment B raw30813step2 raw30813step2Labels := by
      have ha : raw30813step2 = -raw30813step1 := by apply Matrix.ext; change ∀ i j, raw30813step2 i j = -(raw30813step1 i j); unfold raw30813step2 raw30813step1; decide +kernel
      have hl : raw30813step2Labels = raw30813step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30813step2 raw30813step2Labels = mixedMoment B raw30813step3 raw30813step3Labels := by
      have ha : raw30813step3 = raw30813step2 := by apply Matrix.ext; unfold raw30813step3 raw30813step2; decide +kernel
      have hl : raw30813step2Labels = labelEmbedding1 ∘ raw30813step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30813step2 raw30813step2Labels raw30813step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3448 node3448Labels := by rfl

def raw30814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30814Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30814step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30814step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30814step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw30814step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30814step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30814step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30814step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30814step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30814 raw30814Labels = mixedMoment B node3448 node3448Labels := by
  calc
    mixedMoment B raw30814 raw30814Labels = mixedMoment B raw30814step0 raw30814step0Labels := by
      have hz : ∀ j, raw30814 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30814step0 = (fun i j => raw30814 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30814step0 raw30814; decide +kernel
      have hl : raw30814step0Labels = raw30814Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30814 raw30814Labels permutation346 hz
    mixedMoment B raw30814step0 raw30814step0Labels = mixedMoment B raw30814step1 raw30814step1Labels := by
      have ha : raw30814step1 = (fun i j => raw30814step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30814step1 raw30814step0; decide +kernel
      have hl : raw30814step1Labels = raw30814step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30814step0 raw30814step0Labels permutation33 permutation7
    mixedMoment B raw30814step1 raw30814step1Labels = mixedMoment B raw30814step2 raw30814step2Labels := by
      have ha : raw30814step2 = -raw30814step1 := by apply Matrix.ext; change ∀ i j, raw30814step2 i j = -(raw30814step1 i j); unfold raw30814step2 raw30814step1; decide +kernel
      have hl : raw30814step2Labels = raw30814step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30814step2 raw30814step2Labels = mixedMoment B raw30814step3 raw30814step3Labels := by
      have ha : raw30814step3 = raw30814step2 := by apply Matrix.ext; unfold raw30814step3 raw30814step2; decide +kernel
      have hl : raw30814step2Labels = labelEmbedding1 ∘ raw30814step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30814step2 raw30814step2Labels raw30814step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3448 node3448Labels := by rfl

def raw30815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30815Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30815step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, -1, 3]]
def raw30815step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30815step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw30815step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30815step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw30815step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30815 raw30815Labels = mixedMoment B node3252 node3252Labels := by
  calc
    mixedMoment B raw30815 raw30815Labels = mixedMoment B raw30815step0 raw30815step0Labels := by
      have hz : ∀ j, raw30815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30815step0 = (fun i j => raw30815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30815step0 raw30815; decide +kernel
      have hl : raw30815step0Labels = raw30815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30815 raw30815Labels permutation346 hz
    mixedMoment B raw30815step0 raw30815step0Labels = mixedMoment B raw30815step1 raw30815step1Labels := by
      have ha : raw30815step1 = (fun i j => raw30815step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30815step1 raw30815step0; decide +kernel
      have hl : raw30815step1Labels = raw30815step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30815step0 raw30815step0Labels permutation33 permutation7
    mixedMoment B raw30815step1 raw30815step1Labels = mixedMoment B raw30815step2 raw30815step2Labels := by
      have ha : raw30815step2 = -raw30815step1 := by apply Matrix.ext; change ∀ i j, raw30815step2 i j = -(raw30815step1 i j); unfold raw30815step2 raw30815step1; decide +kernel
      have hl : raw30815step2Labels = raw30815step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30815step2 raw30815step2Labels = mixedMoment B raw30815step3 raw30815step3Labels := by
      have ha : raw30815step3 = raw30815step2 := by apply Matrix.ext; unfold raw30815step3 raw30815step2; decide +kernel
      have hl : raw30815step2Labels = labelEmbedding1 ∘ raw30815step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30815step2 raw30815step2Labels raw30815step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3252 node3252Labels := by rfl

def raw30816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30816Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30816step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw30816step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw30816step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30816 raw30816Labels = mixedMoment B node3325 node3325Labels := by
  calc
    mixedMoment B raw30816 raw30816Labels = mixedMoment B raw30816step0 raw30816step0Labels := by
      have hz : ∀ j, raw30816 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30816step0 = (fun i j => raw30816 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30816step0 raw30816; decide +kernel
      have hl : raw30816step0Labels = raw30816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30816 raw30816Labels permutation346 hz
    mixedMoment B raw30816step0 raw30816step0Labels = mixedMoment B raw30816step1 raw30816step1Labels := by
      have ha : raw30816step1 = (fun i j => raw30816step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30816step1 raw30816step0; decide +kernel
      have hl : raw30816step1Labels = raw30816step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30816step0 raw30816step0Labels permutation127 permutation7
    mixedMoment B raw30816step1 raw30816step1Labels = mixedMoment B raw30816step2 raw30816step2Labels := by
      have ha : raw30816step2 = raw30816step1 := by apply Matrix.ext; unfold raw30816step2 raw30816step1; decide +kernel
      have hl : raw30816step1Labels = labelEmbedding1 ∘ raw30816step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30816step1 raw30816step1Labels raw30816step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3325 node3325Labels := by rfl

def raw30817 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30817Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30817step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw30817step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30817step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw30817step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30817 raw30817Labels = mixedMoment B node3315 node3315Labels := by
  calc
    mixedMoment B raw30817 raw30817Labels = mixedMoment B raw30817step0 raw30817step0Labels := by
      have ha : raw30817step0 = (fun i j => raw30817 (permutation584 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30817step0 raw30817; decide +kernel
      have hl : raw30817step0Labels = raw30817Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30817 raw30817Labels permutation584 permutation7
    mixedMoment B raw30817step0 raw30817step0Labels = mixedMoment B raw30817step1 raw30817step1Labels := by
      have ha : raw30817step1 = raw30817step0 := by apply Matrix.ext; unfold raw30817step1 raw30817step0; decide +kernel
      have hl : raw30817step0Labels = labelEmbedding1 ∘ raw30817step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30817step0 raw30817step0Labels raw30817step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3315 node3315Labels := by rfl

def raw30818 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30818Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![3, -1, -2], ![2, 0, -2]]
def raw30818step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30818step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30818step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30818 raw30818Labels = mixedMoment B node3327 node3327Labels := by
  calc
    mixedMoment B raw30818 raw30818Labels = mixedMoment B raw30818step0 raw30818step0Labels := by
      have hz : ∀ j, raw30818 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30818step0 = (fun i j => raw30818 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30818step0 raw30818; decide +kernel
      have hl : raw30818step0Labels = raw30818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30818 raw30818Labels permutation346 hz
    mixedMoment B raw30818step0 raw30818step0Labels = mixedMoment B raw30818step1 raw30818step1Labels := by
      have ha : raw30818step1 = (fun i j => raw30818step0 (permutation125 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30818step1 raw30818step0; decide +kernel
      have hl : raw30818step1Labels = raw30818step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30818step0 raw30818step0Labels permutation125 permutation7
    mixedMoment B raw30818step1 raw30818step1Labels = mixedMoment B raw30818step2 raw30818step2Labels := by
      have ha : raw30818step2 = raw30818step1 := by apply Matrix.ext; unfold raw30818step2 raw30818step1; decide +kernel
      have hl : raw30818step1Labels = labelEmbedding1 ∘ raw30818step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30818step1 raw30818step1Labels raw30818step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3327 node3327Labels := by rfl

def raw30819 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw30819Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![3, -1, -2], ![1, 1, -2]]
def raw30819step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw30819step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw30819step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30819 raw30819Labels = mixedMoment B node3353 node3353Labels := by
  calc
    mixedMoment B raw30819 raw30819Labels = mixedMoment B raw30819step0 raw30819step0Labels := by
      have hz : ∀ j, raw30819 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30819step0 = (fun i j => raw30819 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30819step0 raw30819; decide +kernel
      have hl : raw30819step0Labels = raw30819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30819 raw30819Labels permutation346 hz
    mixedMoment B raw30819step0 raw30819step0Labels = mixedMoment B raw30819step1 raw30819step1Labels := by
      have ha : raw30819step1 = (fun i j => raw30819step0 (permutation127 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30819step1 raw30819step0; decide +kernel
      have hl : raw30819step1Labels = raw30819step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30819step0 raw30819step0Labels permutation127 permutation7
    mixedMoment B raw30819step1 raw30819step1Labels = mixedMoment B raw30819step2 raw30819step2Labels := by
      have ha : raw30819step2 = raw30819step1 := by apply Matrix.ext; unfold raw30819step2 raw30819step1; decide +kernel
      have hl : raw30819step1Labels = labelEmbedding1 ∘ raw30819step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30819step1 raw30819step1Labels raw30819step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3353 node3353Labels := by rfl

def raw30820 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30820Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30820step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-2, -1, 3]]
def raw30820step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw30820step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30820step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![2, 1, -3]]
def raw30820step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30820 raw30820Labels = mixedMoment B node3252 node3252Labels := by
  calc
    mixedMoment B raw30820 raw30820Labels = mixedMoment B raw30820step0 raw30820step0Labels := by
      have hz : ∀ j, raw30820 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30820step0 = (fun i j => raw30820 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30820step0 raw30820; decide +kernel
      have hl : raw30820step0Labels = raw30820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30820 raw30820Labels permutation346 hz
    mixedMoment B raw30820step0 raw30820step0Labels = mixedMoment B raw30820step1 raw30820step1Labels := by
      have ha : raw30820step1 = (fun i j => raw30820step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30820step1 raw30820step0; decide +kernel
      have hl : raw30820step1Labels = raw30820step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30820step0 raw30820step0Labels permutation32 permutation7
    mixedMoment B raw30820step1 raw30820step1Labels = mixedMoment B raw30820step2 raw30820step2Labels := by
      have ha : raw30820step2 = -raw30820step1 := by apply Matrix.ext; change ∀ i j, raw30820step2 i j = -(raw30820step1 i j); unfold raw30820step2 raw30820step1; decide +kernel
      have hl : raw30820step2Labels = raw30820step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30820step2 raw30820step2Labels = mixedMoment B raw30820step3 raw30820step3Labels := by
      have ha : raw30820step3 = raw30820step2 := by apply Matrix.ext; unfold raw30820step3 raw30820step2; decide +kernel
      have hl : raw30820step2Labels = labelEmbedding1 ∘ raw30820step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30820step2 raw30820step2Labels raw30820step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3252 node3252Labels := by rfl

def raw30821 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30821Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30821step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw30821step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30821step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![2, 1, -3]]
def raw30821step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30821 raw30821Labels = mixedMoment B node3325 node3325Labels := by
  calc
    mixedMoment B raw30821 raw30821Labels = mixedMoment B raw30821step0 raw30821step0Labels := by
      have hz : ∀ j, raw30821 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30821step0 = (fun i j => raw30821 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30821step0 raw30821; decide +kernel
      have hl : raw30821step0Labels = raw30821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30821 raw30821Labels permutation346 hz
    mixedMoment B raw30821step0 raw30821step0Labels = mixedMoment B raw30821step1 raw30821step1Labels := by
      have ha : raw30821step1 = (fun i j => raw30821step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30821step1 raw30821step0; decide +kernel
      have hl : raw30821step1Labels = raw30821step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30821step0 raw30821step0Labels permutation151 permutation7
    mixedMoment B raw30821step1 raw30821step1Labels = mixedMoment B raw30821step2 raw30821step2Labels := by
      have ha : raw30821step2 = raw30821step1 := by apply Matrix.ext; unfold raw30821step2 raw30821step1; decide +kernel
      have hl : raw30821step1Labels = labelEmbedding1 ∘ raw30821step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30821step1 raw30821step1Labels raw30821step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3325 node3325Labels := by rfl

def raw30822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30822Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30822step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw30822step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30822step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw30822step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30822 raw30822Labels = mixedMoment B node3315 node3315Labels := by
  calc
    mixedMoment B raw30822 raw30822Labels = mixedMoment B raw30822step0 raw30822step0Labels := by
      have ha : raw30822step0 = (fun i j => raw30822 (permutation682 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30822step0 raw30822; decide +kernel
      have hl : raw30822step0Labels = raw30822Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30822 raw30822Labels permutation682 permutation7
    mixedMoment B raw30822step0 raw30822step0Labels = mixedMoment B raw30822step1 raw30822step1Labels := by
      have ha : raw30822step1 = raw30822step0 := by apply Matrix.ext; unfold raw30822step1 raw30822step0; decide +kernel
      have hl : raw30822step0Labels = labelEmbedding1 ∘ raw30822step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30822step0 raw30822step0Labels raw30822step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3315 node3315Labels := by rfl

def raw30823 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30823Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30823step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30823step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30823step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw30823step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30823 raw30823Labels = mixedMoment B node3327 node3327Labels := by
  calc
    mixedMoment B raw30823 raw30823Labels = mixedMoment B raw30823step0 raw30823step0Labels := by
      have hz : ∀ j, raw30823 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30823step0 = (fun i j => raw30823 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30823step0 raw30823; decide +kernel
      have hl : raw30823step0Labels = raw30823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30823 raw30823Labels permutation346 hz
    mixedMoment B raw30823step0 raw30823step0Labels = mixedMoment B raw30823step1 raw30823step1Labels := by
      have ha : raw30823step1 = (fun i j => raw30823step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30823step1 raw30823step0; decide +kernel
      have hl : raw30823step1Labels = raw30823step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30823step0 raw30823step0Labels permutation149 permutation7
    mixedMoment B raw30823step1 raw30823step1Labels = mixedMoment B raw30823step2 raw30823step2Labels := by
      have ha : raw30823step2 = raw30823step1 := by apply Matrix.ext; unfold raw30823step2 raw30823step1; decide +kernel
      have hl : raw30823step1Labels = labelEmbedding1 ∘ raw30823step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30823step1 raw30823step1Labels raw30823step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3327 node3327Labels := by rfl

def raw30824 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw30824Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw30824step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw30824step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw30824step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30824 raw30824Labels = mixedMoment B node3353 node3353Labels := by
  calc
    mixedMoment B raw30824 raw30824Labels = mixedMoment B raw30824step0 raw30824step0Labels := by
      have hz : ∀ j, raw30824 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30824step0 = (fun i j => raw30824 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30824step0 raw30824; decide +kernel
      have hl : raw30824step0Labels = raw30824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30824 raw30824Labels permutation346 hz
    mixedMoment B raw30824step0 raw30824step0Labels = mixedMoment B raw30824step1 raw30824step1Labels := by
      have ha : raw30824step1 = (fun i j => raw30824step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30824step1 raw30824step0; decide +kernel
      have hl : raw30824step1Labels = raw30824step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30824step0 raw30824step0Labels permutation151 permutation7
    mixedMoment B raw30824step1 raw30824step1Labels = mixedMoment B raw30824step2 raw30824step2Labels := by
      have ha : raw30824step2 = raw30824step1 := by apply Matrix.ext; unfold raw30824step2 raw30824step1; decide +kernel
      have hl : raw30824step1Labels = labelEmbedding1 ∘ raw30824step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30824step1 raw30824step1Labels raw30824step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3353 node3353Labels := by rfl

def raw30825 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30825Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30825step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30825step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30825 raw30825Labels = mixedMoment B node1106 node1106Labels := by
  calc
    mixedMoment B raw30825 raw30825Labels = mixedMoment B raw30825step0 raw30825step0Labels := by
      have ha : raw30825step0 = (fun i j => raw30825 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30825step0 raw30825; decide +kernel
      have hl : raw30825step0Labels = raw30825Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30825 raw30825Labels permutation158 permutation2
    _ = mixedMoment B node1106 node1106Labels := by rfl

def raw30826 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30826Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30826step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30826step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30826 raw30826Labels = mixedMoment B node2316 node2316Labels := by
  calc
    mixedMoment B raw30826 raw30826Labels = mixedMoment B raw30826step0 raw30826step0Labels := by
      have ha : raw30826step0 = (fun i j => raw30826 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30826step0 raw30826; decide +kernel
      have hl : raw30826step0Labels = raw30826Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30826 raw30826Labels permutation158 permutation2
    _ = mixedMoment B node2316 node2316Labels := by rfl

def raw30827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30827Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30827step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30827 raw30827Labels = mixedMoment B node2414 node2414Labels := by
  calc
    mixedMoment B raw30827 raw30827Labels = mixedMoment B raw30827step0 raw30827step0Labels := by
      have ha : raw30827step0 = (fun i j => raw30827 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30827step0 raw30827; decide +kernel
      have hl : raw30827step0Labels = raw30827Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30827 raw30827Labels permutation158 permutation2
    _ = mixedMoment B node2414 node2414Labels := by rfl

def raw30828 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2], ![1, 1, -2]]
def raw30828Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw30828step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30828 raw30828Labels = mixedMoment B node2459 node2459Labels := by
  calc
    mixedMoment B raw30828 raw30828Labels = mixedMoment B raw30828step0 raw30828step0Labels := by
      have ha : raw30828step0 = (fun i j => raw30828 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30828step0 raw30828; decide +kernel
      have hl : raw30828step0Labels = raw30828Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30828 raw30828Labels permutation159 permutation2
    _ = mixedMoment B node2459 node2459Labels := by rfl

def raw30829 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30829step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30829step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30829step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw30829step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30829step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw30829step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30829 raw30829Labels = mixedMoment B node5193 node5193Labels := by
  calc
    mixedMoment B raw30829 raw30829Labels = mixedMoment B raw30829step0 raw30829step0Labels := by
      have hz : ∀ j, raw30829 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30829step0 = (fun i j => raw30829 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30829step0 raw30829; decide +kernel
      have hl : raw30829step0Labels = raw30829Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30829 raw30829Labels permutation346 hz
    mixedMoment B raw30829step0 raw30829step0Labels = mixedMoment B raw30829step1 raw30829step1Labels := by
      have ha : raw30829step1 = (fun i j => raw30829step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30829step1 raw30829step0; decide +kernel
      have hl : raw30829step1Labels = raw30829step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30829step0 raw30829step0Labels permutation32 permutation7
    mixedMoment B raw30829step1 raw30829step1Labels = mixedMoment B raw30829step2 raw30829step2Labels := by
      have ha : raw30829step2 = raw30829step1 := by apply Matrix.ext; unfold raw30829step2 raw30829step1; decide +kernel
      have hl : raw30829step1Labels = labelEmbedding10 ∘ raw30829step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30829step1 raw30829step1Labels raw30829step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5193 node5193Labels := by rfl

def raw30830 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30830step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw30830step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30830step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw30830step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30830 raw30830Labels = mixedMoment B node5142 node5142Labels := by
  calc
    mixedMoment B raw30830 raw30830Labels = mixedMoment B raw30830step0 raw30830step0Labels := by
      have ha : raw30830step0 = (fun i j => raw30830 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30830step0 raw30830; decide +kernel
      have hl : raw30830step0Labels = raw30830Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30830 raw30830Labels permutation152 permutation7
    mixedMoment B raw30830step0 raw30830step0Labels = mixedMoment B raw30830step1 raw30830step1Labels := by
      have ha : raw30830step1 = raw30830step0 := by apply Matrix.ext; unfold raw30830step1 raw30830step0; decide +kernel
      have hl : raw30830step0Labels = labelEmbedding10 ∘ raw30830step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30830step0 raw30830step0Labels raw30830step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5142 node5142Labels := by rfl

def raw30831 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw30831step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30831step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw30831step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30831 raw30831Labels = mixedMoment B node5156 node5156Labels := by
  calc
    mixedMoment B raw30831 raw30831Labels = mixedMoment B raw30831step0 raw30831step0Labels := by
      have hz : ∀ j, raw30831 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30831step0 = (fun i j => raw30831 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30831step0 raw30831; decide +kernel
      have hl : raw30831step0Labels = raw30831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30831 raw30831Labels permutation346 hz
    mixedMoment B raw30831step0 raw30831step0Labels = mixedMoment B raw30831step1 raw30831step1Labels := by
      have ha : raw30831step1 = (fun i j => raw30831step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30831step1 raw30831step0; decide +kernel
      have hl : raw30831step1Labels = raw30831step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30831step0 raw30831step0Labels permutation32 permutation7
    mixedMoment B raw30831step1 raw30831step1Labels = mixedMoment B raw30831step2 raw30831step2Labels := by
      have ha : raw30831step2 = raw30831step1 := by apply Matrix.ext; unfold raw30831step2 raw30831step1; decide +kernel
      have hl : raw30831step1Labels = labelEmbedding10 ∘ raw30831step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30831step1 raw30831step1Labels raw30831step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5156 node5156Labels := by rfl

def raw30832 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw30832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw30832step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30832step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30832step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30832step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30832 raw30832Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw30832 raw30832Labels = mixedMoment B raw30832step0 raw30832step0Labels := by
      have hz : ∀ j, raw30832 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30832step0 = (fun i j => raw30832 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30832step0 raw30832; decide +kernel
      have hl : raw30832step0Labels = raw30832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30832 raw30832Labels permutation346 hz
    mixedMoment B raw30832step0 raw30832step0Labels = mixedMoment B raw30832step1 raw30832step1Labels := by
      have ha : raw30832step1 = (fun i j => raw30832step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30832step1 raw30832step0; decide +kernel
      have hl : raw30832step1Labels = raw30832step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30832step0 raw30832step0Labels permutation33 permutation7
    mixedMoment B raw30832step1 raw30832step1Labels = mixedMoment B raw30832step2 raw30832step2Labels := by
      have ha : raw30832step2 = raw30832step1 := by apply Matrix.ext; unfold raw30832step2 raw30832step1; decide +kernel
      have hl : raw30832step1Labels = labelEmbedding10 ∘ raw30832step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30832step1 raw30832step1Labels raw30832step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw30833 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30833step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![-2, 0, 2]]
def raw30833step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30833step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30833step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30833step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw30833step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30833 raw30833Labels = mixedMoment B node4711 node4711Labels := by
  calc
    mixedMoment B raw30833 raw30833Labels = mixedMoment B raw30833step0 raw30833step0Labels := by
      have ha : raw30833step0 = (fun i j => raw30833 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30833step0 raw30833; decide +kernel
      have hl : raw30833step0Labels = raw30833Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30833 raw30833Labels permutation158 permutation4
    mixedMoment B raw30833step0 raw30833step0Labels = mixedMoment B raw30833step1 raw30833step1Labels := by
      have ha : raw30833step1 = -raw30833step0 := by apply Matrix.ext; change ∀ i j, raw30833step1 i j = -(raw30833step0 i j); unfold raw30833step1 raw30833step0; decide +kernel
      have hl : raw30833step1Labels = raw30833step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30833step1 raw30833step1Labels = mixedMoment B raw30833step2 raw30833step2Labels := by
      have ha : raw30833step2 = raw30833step1 := by apply Matrix.ext; unfold raw30833step2 raw30833step1; decide +kernel
      have hl : raw30833step1Labels = labelEmbedding7 ∘ raw30833step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30833step1 raw30833step1Labels raw30833step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4711 node4711Labels := by rfl

def raw30834 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30834step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw30834step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30834step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw30834step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30834 raw30834Labels = mixedMoment B node4988 node4988Labels := by
  calc
    mixedMoment B raw30834 raw30834Labels = mixedMoment B raw30834step0 raw30834step0Labels := by
      have ha : raw30834step0 = (fun i j => raw30834 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30834step0 raw30834; decide +kernel
      have hl : raw30834step0Labels = raw30834Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30834 raw30834Labels permutation158 permutation6
    mixedMoment B raw30834step0 raw30834step0Labels = mixedMoment B raw30834step1 raw30834step1Labels := by
      have ha : raw30834step1 = raw30834step0 := by apply Matrix.ext; unfold raw30834step1 raw30834step0; decide +kernel
      have hl : raw30834step0Labels = labelEmbedding9 ∘ raw30834step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30834step0 raw30834step0Labels raw30834step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4988 node4988Labels := by rfl

def raw30835 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30835step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw30835step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30835step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2], ![2, 0, -2]]
def raw30835step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30835 raw30835Labels = mixedMoment B node5045 node5045Labels := by
  calc
    mixedMoment B raw30835 raw30835Labels = mixedMoment B raw30835step0 raw30835step0Labels := by
      have ha : raw30835step0 = (fun i j => raw30835 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30835step0 raw30835; decide +kernel
      have hl : raw30835step0Labels = raw30835Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30835 raw30835Labels permutation158 permutation6
    mixedMoment B raw30835step0 raw30835step0Labels = mixedMoment B raw30835step1 raw30835step1Labels := by
      have ha : raw30835step1 = raw30835step0 := by apply Matrix.ext; unfold raw30835step1 raw30835step0; decide +kernel
      have hl : raw30835step0Labels = labelEmbedding9 ∘ raw30835step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30835step0 raw30835step0Labels raw30835step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5045 node5045Labels := by rfl

def raw30836 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30836step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30836step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, -2, 2], ![0, -2, 2]]
def raw30836step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30836step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw30836step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw30836step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw30836step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw30836step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw30836step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical30836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30836 raw30836Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw30836 raw30836Labels = mixedMoment B raw30836step0 raw30836step0Labels := by
      have hz : ∀ j, raw30836 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30836step0 = (fun i j => raw30836 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30836step0 raw30836; decide +kernel
      have hl : raw30836step0Labels = raw30836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30836 raw30836Labels permutation434 hz
    mixedMoment B raw30836step0 raw30836step0Labels = mixedMoment B raw30836step1 raw30836step1Labels := by
      have hz : ∀ j, raw30836step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30836step1 = (fun i j => raw30836step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30836step1 raw30836step0; decide +kernel
      have hl : raw30836step1Labels = raw30836step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30836step0 raw30836step0Labels permutation80 hz
    mixedMoment B raw30836step1 raw30836step1Labels = mixedMoment B raw30836step2 raw30836step2Labels := by
      have hz : ∀ i, raw30836step1 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw30836step2 = (fun i j => raw30836step1 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw30836step2 raw30836step1; decide +kernel
      have hl : raw30836step2Labels = (fun j => raw30836step1Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw30836step1 raw30836step1Labels permutation2 hz
    mixedMoment B raw30836step2 raw30836step2Labels = mixedMoment B raw30836step3 raw30836step3Labels := by
      have ha : raw30836step3 = -raw30836step2 := by apply Matrix.ext; change ∀ i j, raw30836step3 i j = -(raw30836step2 i j); unfold raw30836step3 raw30836step2; decide +kernel
      have hl : raw30836step3Labels = raw30836step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30836step3 raw30836step3Labels = mixedMoment B raw30836step4 raw30836step4Labels := by
      have ha : raw30836step4 = raw30836step3 := by apply Matrix.ext; unfold raw30836step4 raw30836step3; decide +kernel
      have hl : raw30836step3Labels = labelEmbedding3 ∘ raw30836step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30836step3 raw30836step3Labels raw30836step4Labels labelEmbedding3 hl
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw30837 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30837step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30837step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, -2, 2], ![0, -2, 2]]
def raw30837step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30837step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw30837step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30837step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, 0, -2], ![2, 0, -2]]
def raw30837step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30837 raw30837Labels = mixedMoment B node5024 node5024Labels := by
  calc
    mixedMoment B raw30837 raw30837Labels = mixedMoment B raw30837step0 raw30837step0Labels := by
      have hz : ∀ j, raw30837 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30837step0 = (fun i j => raw30837 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30837step0 raw30837; decide +kernel
      have hl : raw30837step0Labels = raw30837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30837 raw30837Labels permutation434 hz
    mixedMoment B raw30837step0 raw30837step0Labels = mixedMoment B raw30837step1 raw30837step1Labels := by
      have hz : ∀ j, raw30837step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30837step1 = (fun i j => raw30837step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30837step1 raw30837step0; decide +kernel
      have hl : raw30837step1Labels = raw30837step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30837step0 raw30837step0Labels permutation80 hz
    mixedMoment B raw30837step1 raw30837step1Labels = mixedMoment B raw30837step2 raw30837step2Labels := by
      have ha : raw30837step2 = (fun i j => raw30837step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30837step2 raw30837step1; decide +kernel
      have hl : raw30837step2Labels = raw30837step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30837step1 raw30837step1Labels permutation8 permutation6
    mixedMoment B raw30837step2 raw30837step2Labels = mixedMoment B raw30837step3 raw30837step3Labels := by
      have ha : raw30837step3 = raw30837step2 := by apply Matrix.ext; unfold raw30837step3 raw30837step2; decide +kernel
      have hl : raw30837step2Labels = labelEmbedding9 ∘ raw30837step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30837step2 raw30837step2Labels raw30837step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5024 node5024Labels := by rfl

def raw30838 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw30838step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30838step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30838step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30838step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw30838step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30838 raw30838Labels = mixedMoment B node5063 node5063Labels := by
  calc
    mixedMoment B raw30838 raw30838Labels = mixedMoment B raw30838step0 raw30838step0Labels := by
      have hz : ∀ j, raw30838 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30838step0 = (fun i j => raw30838 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30838step0 raw30838; decide +kernel
      have hl : raw30838step0Labels = raw30838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30838 raw30838Labels permutation434 hz
    mixedMoment B raw30838step0 raw30838step0Labels = mixedMoment B raw30838step1 raw30838step1Labels := by
      have ha : raw30838step1 = (fun i j => raw30838step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30838step1 raw30838step0; decide +kernel
      have hl : raw30838step1Labels = raw30838step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30838step0 raw30838step0Labels permutation32 permutation6
    mixedMoment B raw30838step1 raw30838step1Labels = mixedMoment B raw30838step2 raw30838step2Labels := by
      have ha : raw30838step2 = raw30838step1 := by apply Matrix.ext; unfold raw30838step2 raw30838step1; decide +kernel
      have hl : raw30838step1Labels = labelEmbedding9 ∘ raw30838step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30838step1 raw30838step1Labels raw30838step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5063 node5063Labels := by rfl

def raw30839 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![0, -2, 2]]
def raw30839Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![0, -2, 2]]
def raw30839step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-3, 1, 2]]
def raw30839step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30839step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw30839step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30839step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw30839step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30839 raw30839Labels = mixedMoment B node4718 node4718Labels := by
  calc
    mixedMoment B raw30839 raw30839Labels = mixedMoment B raw30839step0 raw30839step0Labels := by
      have hz : ∀ j, raw30839 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30839step0 = (fun i j => raw30839 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30839step0 raw30839; decide +kernel
      have hl : raw30839step0Labels = raw30839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30839 raw30839Labels permutation346 hz
    mixedMoment B raw30839step0 raw30839step0Labels = mixedMoment B raw30839step1 raw30839step1Labels := by
      have ha : raw30839step1 = (fun i j => raw30839step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30839step1 raw30839step0; decide +kernel
      have hl : raw30839step1Labels = raw30839step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30839step0 raw30839step0Labels permutation33 permutation4
    mixedMoment B raw30839step1 raw30839step1Labels = mixedMoment B raw30839step2 raw30839step2Labels := by
      have ha : raw30839step2 = -raw30839step1 := by apply Matrix.ext; change ∀ i j, raw30839step2 i j = -(raw30839step1 i j); unfold raw30839step2 raw30839step1; decide +kernel
      have hl : raw30839step2Labels = raw30839step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30839step2 raw30839step2Labels = mixedMoment B raw30839step3 raw30839step3Labels := by
      have ha : raw30839step3 = raw30839step2 := by apply Matrix.ext; unfold raw30839step3 raw30839step2; decide +kernel
      have hl : raw30839step2Labels = labelEmbedding7 ∘ raw30839step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30839step2 raw30839step2Labels raw30839step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4718 node4718Labels := by rfl

def raw30840 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![0, -2, 2]]
def raw30840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![1, -3, 2], ![0, -2, 2]]
def raw30840step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw30840step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw30840step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30840 raw30840Labels = mixedMoment B node4914 node4914Labels := by
  calc
    mixedMoment B raw30840 raw30840Labels = mixedMoment B raw30840step0 raw30840step0Labels := by
      have hz : ∀ j, raw30840 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30840step0 = (fun i j => raw30840 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30840step0 raw30840; decide +kernel
      have hl : raw30840step0Labels = raw30840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30840 raw30840Labels permutation346 hz
    mixedMoment B raw30840step0 raw30840step0Labels = mixedMoment B raw30840step1 raw30840step1Labels := by
      have ha : raw30840step1 = (fun i j => raw30840step0 (permutation127 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30840step1 raw30840step0; decide +kernel
      have hl : raw30840step1Labels = raw30840step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30840step0 raw30840step0Labels permutation127 permutation4
    mixedMoment B raw30840step1 raw30840step1Labels = mixedMoment B raw30840step2 raw30840step2Labels := by
      have ha : raw30840step2 = raw30840step1 := by apply Matrix.ext; unfold raw30840step2 raw30840step1; decide +kernel
      have hl : raw30840step1Labels = labelEmbedding7 ∘ raw30840step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30840step1 raw30840step1Labels raw30840step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4914 node4914Labels := by rfl

def raw30841 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -3, 2], ![0, -2, 2]]
def raw30841Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30841step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw30841step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30841step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw30841step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30841 raw30841Labels = mixedMoment B node4909 node4909Labels := by
  calc
    mixedMoment B raw30841 raw30841Labels = mixedMoment B raw30841step0 raw30841step0Labels := by
      have ha : raw30841step0 = (fun i j => raw30841 (permutation584 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30841step0 raw30841; decide +kernel
      have hl : raw30841step0Labels = raw30841Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30841 raw30841Labels permutation584 permutation4
    mixedMoment B raw30841step0 raw30841step0Labels = mixedMoment B raw30841step1 raw30841step1Labels := by
      have ha : raw30841step1 = raw30841step0 := by apply Matrix.ext; unfold raw30841step1 raw30841step0; decide +kernel
      have hl : raw30841step0Labels = labelEmbedding7 ∘ raw30841step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30841step0 raw30841step0Labels raw30841step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4909 node4909Labels := by rfl

def raw30842 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -3, 2], ![0, -2, 2]]
def raw30842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-2, 2, 0], ![1, -3, 2], ![0, -2, 2]]
def raw30842step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30842step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30842step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30842step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30842 raw30842Labels = mixedMoment B node4920 node4920Labels := by
  calc
    mixedMoment B raw30842 raw30842Labels = mixedMoment B raw30842step0 raw30842step0Labels := by
      have hz : ∀ j, raw30842 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30842step0 = (fun i j => raw30842 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30842step0 raw30842; decide +kernel
      have hl : raw30842step0Labels = raw30842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30842 raw30842Labels permutation346 hz
    mixedMoment B raw30842step0 raw30842step0Labels = mixedMoment B raw30842step1 raw30842step1Labels := by
      have ha : raw30842step1 = (fun i j => raw30842step0 (permutation125 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30842step1 raw30842step0; decide +kernel
      have hl : raw30842step1Labels = raw30842step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30842step0 raw30842step0Labels permutation125 permutation4
    mixedMoment B raw30842step1 raw30842step1Labels = mixedMoment B raw30842step2 raw30842step2Labels := by
      have ha : raw30842step2 = raw30842step1 := by apply Matrix.ext; unfold raw30842step2 raw30842step1; decide +kernel
      have hl : raw30842step1Labels = labelEmbedding7 ∘ raw30842step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30842step1 raw30842step1Labels raw30842step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4920 node4920Labels := by rfl

def raw30843 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -3, 2]]
def raw30843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -3, 2]]
def raw30843step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30843step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-3, 1, 2]]
def raw30843step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30843step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw30843step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30843step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw30843step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30843 raw30843Labels = mixedMoment B node4718 node4718Labels := by
  calc
    mixedMoment B raw30843 raw30843Labels = mixedMoment B raw30843step0 raw30843step0Labels := by
      have hz : ∀ j, raw30843 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30843step0 = (fun i j => raw30843 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30843step0 raw30843; decide +kernel
      have hl : raw30843step0Labels = raw30843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30843 raw30843Labels permutation346 hz
    mixedMoment B raw30843step0 raw30843step0Labels = mixedMoment B raw30843step1 raw30843step1Labels := by
      have ha : raw30843step1 = (fun i j => raw30843step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30843step1 raw30843step0; decide +kernel
      have hl : raw30843step1Labels = raw30843step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30843step0 raw30843step0Labels permutation32 permutation4
    mixedMoment B raw30843step1 raw30843step1Labels = mixedMoment B raw30843step2 raw30843step2Labels := by
      have ha : raw30843step2 = -raw30843step1 := by apply Matrix.ext; change ∀ i j, raw30843step2 i j = -(raw30843step1 i j); unfold raw30843step2 raw30843step1; decide +kernel
      have hl : raw30843step2Labels = raw30843step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30843step2 raw30843step2Labels = mixedMoment B raw30843step3 raw30843step3Labels := by
      have ha : raw30843step3 = raw30843step2 := by apply Matrix.ext; unfold raw30843step3 raw30843step2; decide +kernel
      have hl : raw30843step2Labels = labelEmbedding7 ∘ raw30843step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30843step2 raw30843step2Labels raw30843step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4718 node4718Labels := by rfl

def raw30844 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -3, 2]]
def raw30844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -3, 2]]
def raw30844step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw30844step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30844step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw30844step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30844 raw30844Labels = mixedMoment B node4914 node4914Labels := by
  calc
    mixedMoment B raw30844 raw30844Labels = mixedMoment B raw30844step0 raw30844step0Labels := by
      have hz : ∀ j, raw30844 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30844step0 = (fun i j => raw30844 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30844step0 raw30844; decide +kernel
      have hl : raw30844step0Labels = raw30844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30844 raw30844Labels permutation346 hz
    mixedMoment B raw30844step0 raw30844step0Labels = mixedMoment B raw30844step1 raw30844step1Labels := by
      have ha : raw30844step1 = (fun i j => raw30844step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30844step1 raw30844step0; decide +kernel
      have hl : raw30844step1Labels = raw30844step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30844step0 raw30844step0Labels permutation151 permutation4
    mixedMoment B raw30844step1 raw30844step1Labels = mixedMoment B raw30844step2 raw30844step2Labels := by
      have ha : raw30844step2 = raw30844step1 := by apply Matrix.ext; unfold raw30844step2 raw30844step1; decide +kernel
      have hl : raw30844step1Labels = labelEmbedding7 ∘ raw30844step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30844step1 raw30844step1Labels raw30844step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4914 node4914Labels := by rfl

def raw30845 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -3, 2]]
def raw30845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw30845step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30845step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw30845step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30845 raw30845Labels = mixedMoment B node4909 node4909Labels := by
  calc
    mixedMoment B raw30845 raw30845Labels = mixedMoment B raw30845step0 raw30845step0Labels := by
      have ha : raw30845step0 = (fun i j => raw30845 (permutation682 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30845step0 raw30845; decide +kernel
      have hl : raw30845step0Labels = raw30845Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30845 raw30845Labels permutation682 permutation4
    mixedMoment B raw30845step0 raw30845step0Labels = mixedMoment B raw30845step1 raw30845step1Labels := by
      have ha : raw30845step1 = raw30845step0 := by apply Matrix.ext; unfold raw30845step1 raw30845step0; decide +kernel
      have hl : raw30845step0Labels = labelEmbedding7 ∘ raw30845step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30845step0 raw30845step0Labels raw30845step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4909 node4909Labels := by rfl

def raw30846 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -2, 2], ![1, -3, 2]]
def raw30846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-2, 2, 0], ![0, -2, 2], ![1, -3, 2]]
def raw30846step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30846step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30846step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30846step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30846step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30846 raw30846Labels = mixedMoment B node4920 node4920Labels := by
  calc
    mixedMoment B raw30846 raw30846Labels = mixedMoment B raw30846step0 raw30846step0Labels := by
      have hz : ∀ j, raw30846 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30846step0 = (fun i j => raw30846 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30846step0 raw30846; decide +kernel
      have hl : raw30846step0Labels = raw30846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30846 raw30846Labels permutation346 hz
    mixedMoment B raw30846step0 raw30846step0Labels = mixedMoment B raw30846step1 raw30846step1Labels := by
      have ha : raw30846step1 = (fun i j => raw30846step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30846step1 raw30846step0; decide +kernel
      have hl : raw30846step1Labels = raw30846step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30846step0 raw30846step0Labels permutation149 permutation4
    mixedMoment B raw30846step1 raw30846step1Labels = mixedMoment B raw30846step2 raw30846step2Labels := by
      have ha : raw30846step2 = raw30846step1 := by apply Matrix.ext; unfold raw30846step2 raw30846step1; decide +kernel
      have hl : raw30846step1Labels = labelEmbedding7 ∘ raw30846step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30846step1 raw30846step1Labels raw30846step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4920 node4920Labels := by rfl

def raw30847 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw30847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![1, -3, 2]]
def raw30847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30847step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw30847step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30847step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw30847step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30847 raw30847Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw30847 raw30847Labels = mixedMoment B raw30847step0 raw30847step0Labels := by
      have hz : ∀ j, raw30847 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30847step0 = (fun i j => raw30847 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30847step0 raw30847; decide +kernel
      have hl : raw30847step0Labels = raw30847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30847 raw30847Labels permutation346 hz
    mixedMoment B raw30847step0 raw30847step0Labels = mixedMoment B raw30847step1 raw30847step1Labels := by
      have ha : raw30847step1 = (fun i j => raw30847step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30847step1 raw30847step0; decide +kernel
      have hl : raw30847step1Labels = raw30847step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30847step0 raw30847step0Labels permutation151 permutation4
    mixedMoment B raw30847step1 raw30847step1Labels = mixedMoment B raw30847step2 raw30847step2Labels := by
      have ha : raw30847step2 = raw30847step1 := by apply Matrix.ext; unfold raw30847step2 raw30847step1; decide +kernel
      have hl : raw30847step1Labels = labelEmbedding7 ∘ raw30847step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30847step1 raw30847step1Labels raw30847step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5014 node5014Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
