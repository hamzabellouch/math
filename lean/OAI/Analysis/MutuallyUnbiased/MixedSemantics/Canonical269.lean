import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34432step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34432 raw34432Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw34432 raw34432Labels = mixedMoment B raw34432step0 raw34432step0Labels := by
      have ha : raw34432step0 = (fun i j => raw34432 (permutation167 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34432step0 raw34432; decide +kernel
      have hl : raw34432step0Labels = raw34432Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34432 raw34432Labels permutation167 permutation2
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw34433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34433step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34433 raw34433Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw34433 raw34433Labels = mixedMoment B raw34433step0 raw34433step0Labels := by
      have ha : raw34433step0 = (fun i j => raw34433 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34433step0 raw34433; decide +kernel
      have hl : raw34433step0Labels = raw34433Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34433 raw34433Labels permutation173 permutation2
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw34434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34434step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34434 raw34434Labels = mixedMoment B node4971 node4971Labels := by
  calc
    mixedMoment B raw34434 raw34434Labels = mixedMoment B raw34434step0 raw34434step0Labels := by
      have ha : raw34434step0 = (fun i j => raw34434 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34434step0 raw34434; decide +kernel
      have hl : raw34434step0Labels = raw34434Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34434 raw34434Labels permutation155 permutation2
    _ = mixedMoment B node4971 node4971Labels := by rfl

def raw34435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw34435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34435step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34435 raw34435Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw34435 raw34435Labels = mixedMoment B raw34435step0 raw34435step0Labels := by
      have ha : raw34435step0 = (fun i j => raw34435 (permutation165 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34435step0 raw34435; decide +kernel
      have hl : raw34435step0Labels = raw34435Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34435 raw34435Labels permutation165 permutation2
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw34436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw34436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34436step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34436 raw34436Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw34436 raw34436Labels = mixedMoment B raw34436step0 raw34436step0Labels := by
      have ha : raw34436step0 = (fun i j => raw34436 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34436step0 raw34436; decide +kernel
      have hl : raw34436step0Labels = raw34436Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34436 raw34436Labels permutation171 permutation2
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw34437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34437step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34437 raw34437Labels = mixedMoment B node4968 node4968Labels := by
  calc
    mixedMoment B raw34437 raw34437Labels = mixedMoment B raw34437step0 raw34437step0Labels := by
      have ha : raw34437step0 = (fun i j => raw34437 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34437step0 raw34437; decide +kernel
      have hl : raw34437step0Labels = raw34437Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34437 raw34437Labels permutation153 permutation2
    _ = mixedMoment B node4968 node4968Labels := by rfl

def raw34438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw34438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw34438step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34438 raw34438Labels = mixedMoment B node5148 node5148Labels := by
  calc
    mixedMoment B raw34438 raw34438Labels = mixedMoment B raw34438step0 raw34438step0Labels := by
      have ha : raw34438step0 = (fun i j => raw34438 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34438step0 raw34438; decide +kernel
      have hl : raw34438step0Labels = raw34438Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34438 raw34438Labels permutation170 permutation2
    _ = mixedMoment B node5148 node5148Labels := by rfl

def raw34439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34439step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34439 raw34439Labels = mixedMoment B node5464 node5464Labels := by
  calc
    mixedMoment B raw34439 raw34439Labels = mixedMoment B raw34439step0 raw34439step0Labels := by
      have ha : raw34439step0 = (fun i j => raw34439 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34439step0 raw34439; decide +kernel
      have hl : raw34439step0Labels = raw34439Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34439 raw34439Labels permutation168 permutation2
    _ = mixedMoment B node5464 node5464Labels := by rfl

def raw34440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34440step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34440step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34440 raw34440Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw34440 raw34440Labels = mixedMoment B raw34440step0 raw34440step0Labels := by
      have hz : ∀ j, raw34440 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34440step0 = (fun i j => raw34440 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34440step0 raw34440; decide +kernel
      have hl : raw34440step0Labels = raw34440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34440 raw34440Labels permutation520 hz
    mixedMoment B raw34440step0 raw34440step0Labels = mixedMoment B raw34440step1 raw34440step1Labels := by
      have ha : raw34440step1 = (fun i j => raw34440step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34440step1 raw34440step0; decide +kernel
      have hl : raw34440step1Labels = raw34440step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34440step0 raw34440step0Labels permutation36 permutation2
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw34441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34441step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34441step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34441 raw34441Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw34441 raw34441Labels = mixedMoment B raw34441step0 raw34441step0Labels := by
      have hz : ∀ j, raw34441 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34441step0 = (fun i j => raw34441 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34441step0 raw34441; decide +kernel
      have hl : raw34441step0Labels = raw34441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34441 raw34441Labels permutation590 hz
    mixedMoment B raw34441step0 raw34441step0Labels = mixedMoment B raw34441step1 raw34441step1Labels := by
      have ha : raw34441step1 = (fun i j => raw34441step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34441step1 raw34441step0; decide +kernel
      have hl : raw34441step1Labels = raw34441step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34441step0 raw34441step0Labels permutation36 permutation2
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw34442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34442step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34442step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34442step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34442 raw34442Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw34442 raw34442Labels = mixedMoment B raw34442step0 raw34442step0Labels := by
      have ha : raw34442step0 = (fun i j => raw34442 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34442step0 raw34442; decide +kernel
      have hl : raw34442step0Labels = raw34442Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34442 raw34442Labels permutation152 permutation3
    mixedMoment B raw34442step0 raw34442step0Labels = mixedMoment B raw34442step1 raw34442step1Labels := by
      have ha : raw34442step1 = raw34442step0 := by apply Matrix.ext; unfold raw34442step1 raw34442step0; decide +kernel
      have hl : raw34442step0Labels = labelEmbedding6 ∘ raw34442step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34442step0 raw34442step0Labels raw34442step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw34443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34443step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34443step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34443step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34443 raw34443Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw34443 raw34443Labels = mixedMoment B raw34443step0 raw34443step0Labels := by
      have ha : raw34443step0 = (fun i j => raw34443 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34443step0 raw34443; decide +kernel
      have hl : raw34443step0Labels = raw34443Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34443 raw34443Labels permutation176 permutation3
    mixedMoment B raw34443step0 raw34443step0Labels = mixedMoment B raw34443step1 raw34443step1Labels := by
      have ha : raw34443step1 = raw34443step0 := by apply Matrix.ext; unfold raw34443step1 raw34443step0; decide +kernel
      have hl : raw34443step0Labels = labelEmbedding6 ∘ raw34443step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34443step0 raw34443step0Labels raw34443step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw34444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34444Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34444step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34444step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34444step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34444 raw34444Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw34444 raw34444Labels = mixedMoment B raw34444step0 raw34444step0Labels := by
      have ha : raw34444step0 = (fun i j => raw34444 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34444step0 raw34444; decide +kernel
      have hl : raw34444step0Labels = raw34444Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34444 raw34444Labels permutation200 permutation3
    mixedMoment B raw34444step0 raw34444step0Labels = mixedMoment B raw34444step1 raw34444step1Labels := by
      have ha : raw34444step1 = raw34444step0 := by apply Matrix.ext; unfold raw34444step1 raw34444step0; decide +kernel
      have hl : raw34444step0Labels = labelEmbedding6 ∘ raw34444step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34444step0 raw34444step0Labels raw34444step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw34445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34445step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34445step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34445step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34445 raw34445Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw34445 raw34445Labels = mixedMoment B raw34445step0 raw34445step0Labels := by
      have hz : ∀ j, raw34445 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34445step0 = (fun i j => raw34445 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34445step0 raw34445; decide +kernel
      have hl : raw34445step0Labels = raw34445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34445 raw34445Labels permutation520 hz
    mixedMoment B raw34445step0 raw34445step0Labels = mixedMoment B raw34445step1 raw34445step1Labels := by
      have ha : raw34445step1 = (fun i j => raw34445step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34445step1 raw34445step0; decide +kernel
      have hl : raw34445step1Labels = raw34445step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34445step0 raw34445step0Labels permutation32 permutation3
    mixedMoment B raw34445step1 raw34445step1Labels = mixedMoment B raw34445step2 raw34445step2Labels := by
      have ha : raw34445step2 = raw34445step1 := by apply Matrix.ext; unfold raw34445step2 raw34445step1; decide +kernel
      have hl : raw34445step1Labels = labelEmbedding6 ∘ raw34445step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34445step1 raw34445step1Labels raw34445step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw34446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34446step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34446step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34446step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34446step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34446 raw34446Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw34446 raw34446Labels = mixedMoment B raw34446step0 raw34446step0Labels := by
      have hz : ∀ j, raw34446 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34446step0 = (fun i j => raw34446 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34446step0 raw34446; decide +kernel
      have hl : raw34446step0Labels = raw34446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34446 raw34446Labels permutation590 hz
    mixedMoment B raw34446step0 raw34446step0Labels = mixedMoment B raw34446step1 raw34446step1Labels := by
      have ha : raw34446step1 = (fun i j => raw34446step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34446step1 raw34446step0; decide +kernel
      have hl : raw34446step1Labels = raw34446step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34446step0 raw34446step0Labels permutation32 permutation3
    mixedMoment B raw34446step1 raw34446step1Labels = mixedMoment B raw34446step2 raw34446step2Labels := by
      have ha : raw34446step2 = raw34446step1 := by apply Matrix.ext; unfold raw34446step2 raw34446step1; decide +kernel
      have hl : raw34446step1Labels = labelEmbedding6 ∘ raw34446step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34446step1 raw34446step1Labels raw34446step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw34447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34447Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34447step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34447step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34447 raw34447Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw34447 raw34447Labels = mixedMoment B raw34447step0 raw34447step0Labels := by
      have ha : raw34447step0 = (fun i j => raw34447 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34447step0 raw34447; decide +kernel
      have hl : raw34447step0Labels = raw34447Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34447 raw34447Labels permutation161 permutation3
    mixedMoment B raw34447step0 raw34447step0Labels = mixedMoment B raw34447step1 raw34447step1Labels := by
      have ha : raw34447step1 = raw34447step0 := by apply Matrix.ext; unfold raw34447step1 raw34447step0; decide +kernel
      have hl : raw34447step0Labels = labelEmbedding6 ∘ raw34447step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34447step0 raw34447step0Labels raw34447step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4344 node4344Labels := by rfl

def raw34448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34448Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34448step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34448step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34448 raw34448Labels = mixedMoment B node4941 node4941Labels := by
  calc
    mixedMoment B raw34448 raw34448Labels = mixedMoment B raw34448step0 raw34448step0Labels := by
      have ha : raw34448step0 = (fun i j => raw34448 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34448step0 raw34448; decide +kernel
      have hl : raw34448step0Labels = raw34448Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34448 raw34448Labels permutation161 permutation3
    mixedMoment B raw34448step0 raw34448step0Labels = mixedMoment B raw34448step1 raw34448step1Labels := by
      have ha : raw34448step1 = raw34448step0 := by apply Matrix.ext; unfold raw34448step1 raw34448step0; decide +kernel
      have hl : raw34448step0Labels = labelEmbedding6 ∘ raw34448step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34448step0 raw34448step0Labels raw34448step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4941 node4941Labels := by rfl

def raw34449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34449Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34449step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34449step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34449step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34449 raw34449Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw34449 raw34449Labels = mixedMoment B raw34449step0 raw34449step0Labels := by
      have ha : raw34449step0 = (fun i j => raw34449 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34449step0 raw34449; decide +kernel
      have hl : raw34449step0Labels = raw34449Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34449 raw34449Labels permutation161 permutation3
    mixedMoment B raw34449step0 raw34449step0Labels = mixedMoment B raw34449step1 raw34449step1Labels := by
      have ha : raw34449step1 = raw34449step0 := by apply Matrix.ext; unfold raw34449step1 raw34449step0; decide +kernel
      have hl : raw34449step0Labels = labelEmbedding6 ∘ raw34449step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34449step0 raw34449step0Labels raw34449step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5137 node5137Labels := by rfl

def raw34450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34450Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34450step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34450step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34450step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34450 raw34450Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw34450 raw34450Labels = mixedMoment B raw34450step0 raw34450step0Labels := by
      have hz : ∀ j, raw34450 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34450step0 = (fun i j => raw34450 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34450step0 raw34450; decide +kernel
      have hl : raw34450step0Labels = raw34450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34450 raw34450Labels permutation520 hz
    mixedMoment B raw34450step0 raw34450step0Labels = mixedMoment B raw34450step1 raw34450step1Labels := by
      have ha : raw34450step1 = (fun i j => raw34450step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34450step1 raw34450step0; decide +kernel
      have hl : raw34450step1Labels = raw34450step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34450step0 raw34450step0Labels permutation35 permutation3
    mixedMoment B raw34450step1 raw34450step1Labels = mixedMoment B raw34450step2 raw34450step2Labels := by
      have ha : raw34450step2 = raw34450step1 := by apply Matrix.ext; unfold raw34450step2 raw34450step1; decide +kernel
      have hl : raw34450step1Labels = labelEmbedding6 ∘ raw34450step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34450step1 raw34450step1Labels raw34450step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw34451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34451Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw34451step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34451step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34451step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34451 raw34451Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw34451 raw34451Labels = mixedMoment B raw34451step0 raw34451step0Labels := by
      have hz : ∀ j, raw34451 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34451step0 = (fun i j => raw34451 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34451step0 raw34451; decide +kernel
      have hl : raw34451step0Labels = raw34451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34451 raw34451Labels permutation590 hz
    mixedMoment B raw34451step0 raw34451step0Labels = mixedMoment B raw34451step1 raw34451step1Labels := by
      have ha : raw34451step1 = (fun i j => raw34451step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34451step1 raw34451step0; decide +kernel
      have hl : raw34451step1Labels = raw34451step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34451step0 raw34451step0Labels permutation35 permutation3
    mixedMoment B raw34451step1 raw34451step1Labels = mixedMoment B raw34451step2 raw34451step2Labels := by
      have ha : raw34451step2 = raw34451step1 := by apply Matrix.ext; unfold raw34451step2 raw34451step1; decide +kernel
      have hl : raw34451step1Labels = labelEmbedding6 ∘ raw34451step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34451step1 raw34451step1Labels raw34451step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw34452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34452Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34452step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34452step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34452 raw34452Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw34452 raw34452Labels = mixedMoment B raw34452step0 raw34452step0Labels := by
      have ha : raw34452step0 = (fun i j => raw34452 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34452step0 raw34452; decide +kernel
      have hl : raw34452step0Labels = raw34452Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34452 raw34452Labels permutation155 permutation3
    mixedMoment B raw34452step0 raw34452step0Labels = mixedMoment B raw34452step1 raw34452step1Labels := by
      have ha : raw34452step1 = raw34452step0 := by apply Matrix.ext; unfold raw34452step1 raw34452step0; decide +kernel
      have hl : raw34452step0Labels = labelEmbedding6 ∘ raw34452step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34452step0 raw34452step0Labels raw34452step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4344 node4344Labels := by rfl

def raw34453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34453Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34453step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34453step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34453step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34453 raw34453Labels = mixedMoment B node4941 node4941Labels := by
  calc
    mixedMoment B raw34453 raw34453Labels = mixedMoment B raw34453step0 raw34453step0Labels := by
      have ha : raw34453step0 = (fun i j => raw34453 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34453step0 raw34453; decide +kernel
      have hl : raw34453step0Labels = raw34453Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34453 raw34453Labels permutation155 permutation3
    mixedMoment B raw34453step0 raw34453step0Labels = mixedMoment B raw34453step1 raw34453step1Labels := by
      have ha : raw34453step1 = raw34453step0 := by apply Matrix.ext; unfold raw34453step1 raw34453step0; decide +kernel
      have hl : raw34453step0Labels = labelEmbedding6 ∘ raw34453step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34453step0 raw34453step0Labels raw34453step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4941 node4941Labels := by rfl

def raw34454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw34454Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34454step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34454step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34454step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34454 raw34454Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw34454 raw34454Labels = mixedMoment B raw34454step0 raw34454step0Labels := by
      have ha : raw34454step0 = (fun i j => raw34454 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34454step0 raw34454; decide +kernel
      have hl : raw34454step0Labels = raw34454Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34454 raw34454Labels permutation155 permutation3
    mixedMoment B raw34454step0 raw34454step0Labels = mixedMoment B raw34454step1 raw34454step1Labels := by
      have ha : raw34454step1 = raw34454step0 := by apply Matrix.ext; unfold raw34454step1 raw34454step0; decide +kernel
      have hl : raw34454step0Labels = labelEmbedding6 ∘ raw34454step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34454step0 raw34454step0Labels raw34454step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5137 node5137Labels := by rfl

def raw34455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw34455Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw34455step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34455step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34455step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34455step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34455 raw34455Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw34455 raw34455Labels = mixedMoment B raw34455step0 raw34455step0Labels := by
      have hz : ∀ j, raw34455 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34455step0 = (fun i j => raw34455 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34455step0 raw34455; decide +kernel
      have hl : raw34455step0Labels = raw34455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34455 raw34455Labels permutation520 hz
    mixedMoment B raw34455step0 raw34455step0Labels = mixedMoment B raw34455step1 raw34455step1Labels := by
      have ha : raw34455step1 = (fun i j => raw34455step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34455step1 raw34455step0; decide +kernel
      have hl : raw34455step1Labels = raw34455step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34455step0 raw34455step0Labels permutation33 permutation3
    mixedMoment B raw34455step1 raw34455step1Labels = mixedMoment B raw34455step2 raw34455step2Labels := by
      have ha : raw34455step2 = raw34455step1 := by apply Matrix.ext; unfold raw34455step2 raw34455step1; decide +kernel
      have hl : raw34455step1Labels = labelEmbedding6 ∘ raw34455step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34455step1 raw34455step1Labels raw34455step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw34456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw34456Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw34456step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34456step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34456step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34456step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34456 raw34456Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw34456 raw34456Labels = mixedMoment B raw34456step0 raw34456step0Labels := by
      have hz : ∀ j, raw34456 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34456step0 = (fun i j => raw34456 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34456step0 raw34456; decide +kernel
      have hl : raw34456step0Labels = raw34456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34456 raw34456Labels permutation590 hz
    mixedMoment B raw34456step0 raw34456step0Labels = mixedMoment B raw34456step1 raw34456step1Labels := by
      have ha : raw34456step1 = (fun i j => raw34456step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34456step1 raw34456step0; decide +kernel
      have hl : raw34456step1Labels = raw34456step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34456step0 raw34456step0Labels permutation33 permutation3
    mixedMoment B raw34456step1 raw34456step1Labels = mixedMoment B raw34456step2 raw34456step2Labels := by
      have ha : raw34456step2 = raw34456step1 := by apply Matrix.ext; unfold raw34456step2 raw34456step1; decide +kernel
      have hl : raw34456step1Labels = labelEmbedding6 ∘ raw34456step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34456step1 raw34456step1Labels raw34456step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw34457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34457step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34457step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34457step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34457 raw34457Labels = mixedMoment B node4341 node4341Labels := by
  calc
    mixedMoment B raw34457 raw34457Labels = mixedMoment B raw34457step0 raw34457step0Labels := by
      have ha : raw34457step0 = (fun i j => raw34457 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34457step0 raw34457; decide +kernel
      have hl : raw34457step0Labels = raw34457Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34457 raw34457Labels permutation153 permutation3
    mixedMoment B raw34457step0 raw34457step0Labels = mixedMoment B raw34457step1 raw34457step1Labels := by
      have ha : raw34457step1 = raw34457step0 := by apply Matrix.ext; unfold raw34457step1 raw34457step0; decide +kernel
      have hl : raw34457step0Labels = labelEmbedding6 ∘ raw34457step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34457step0 raw34457step0Labels raw34457step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4341 node4341Labels := by rfl

def raw34458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34458step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34458step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34458step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34458 raw34458Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw34458 raw34458Labels = mixedMoment B raw34458step0 raw34458step0Labels := by
      have ha : raw34458step0 = (fun i j => raw34458 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34458step0 raw34458; decide +kernel
      have hl : raw34458step0Labels = raw34458Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34458 raw34458Labels permutation153 permutation3
    mixedMoment B raw34458step0 raw34458step0Labels = mixedMoment B raw34458step1 raw34458step1Labels := by
      have ha : raw34458step1 = raw34458step0 := by apply Matrix.ext; unfold raw34458step1 raw34458step0; decide +kernel
      have hl : raw34458step0Labels = labelEmbedding6 ∘ raw34458step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34458step0 raw34458step0Labels raw34458step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4939 node4939Labels := by rfl

def raw34459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34459Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34459step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34459step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34459step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34459 raw34459Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw34459 raw34459Labels = mixedMoment B raw34459step0 raw34459step0Labels := by
      have ha : raw34459step0 = (fun i j => raw34459 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34459step0 raw34459; decide +kernel
      have hl : raw34459step0Labels = raw34459Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34459 raw34459Labels permutation153 permutation3
    mixedMoment B raw34459step0 raw34459step0Labels = mixedMoment B raw34459step1 raw34459step1Labels := by
      have ha : raw34459step1 = raw34459step0 := by apply Matrix.ext; unfold raw34459step1 raw34459step0; decide +kernel
      have hl : raw34459step0Labels = labelEmbedding6 ∘ raw34459step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34459step0 raw34459step0Labels raw34459step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw34460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw34460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34460step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34460step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34460step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34460 raw34460Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw34460 raw34460Labels = mixedMoment B raw34460step0 raw34460step0Labels := by
      have ha : raw34460step0 = (fun i j => raw34460 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34460step0 raw34460; decide +kernel
      have hl : raw34460step0Labels = raw34460Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34460 raw34460Labels permutation159 permutation3
    mixedMoment B raw34460step0 raw34460step0Labels = mixedMoment B raw34460step1 raw34460step1Labels := by
      have ha : raw34460step1 = raw34460step0 := by apply Matrix.ext; unfold raw34460step1 raw34460step0; decide +kernel
      have hl : raw34460step0Labels = labelEmbedding6 ∘ raw34460step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34460step0 raw34460step0Labels raw34460step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw34461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0], ![0, 0, 0]]
def raw34461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34461step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34461step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34461step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34461step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34461 raw34461Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw34461 raw34461Labels = mixedMoment B raw34461step0 raw34461step0Labels := by
      have hz : ∀ j, raw34461 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw34461step0 = (fun i j => raw34461 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw34461step0 raw34461; decide +kernel
      have hl : raw34461step0Labels = raw34461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34461 raw34461Labels permutation590 hz
    mixedMoment B raw34461step0 raw34461step0Labels = mixedMoment B raw34461step1 raw34461step1Labels := by
      have ha : raw34461step1 = (fun i j => raw34461step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34461step1 raw34461step0; decide +kernel
      have hl : raw34461step1Labels = raw34461step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34461step0 raw34461step0Labels permutation32 permutation3
    mixedMoment B raw34461step1 raw34461step1Labels = mixedMoment B raw34461step2 raw34461step2Labels := by
      have ha : raw34461step2 = raw34461step1 := by apply Matrix.ext; unfold raw34461step2 raw34461step1; decide +kernel
      have hl : raw34461step1Labels = labelEmbedding6 ∘ raw34461step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34461step1 raw34461step1Labels raw34461step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5168 node5168Labels := by rfl

def raw34462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34462step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34462step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34462step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34462 raw34462Labels = mixedMoment B node4341 node4341Labels := by
  calc
    mixedMoment B raw34462 raw34462Labels = mixedMoment B raw34462step0 raw34462step0Labels := by
      have ha : raw34462step0 = (fun i j => raw34462 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34462step0 raw34462; decide +kernel
      have hl : raw34462step0Labels = raw34462Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34462 raw34462Labels permutation152 permutation3
    mixedMoment B raw34462step0 raw34462step0Labels = mixedMoment B raw34462step1 raw34462step1Labels := by
      have ha : raw34462step1 = raw34462step0 := by apply Matrix.ext; unfold raw34462step1 raw34462step0; decide +kernel
      have hl : raw34462step0Labels = labelEmbedding6 ∘ raw34462step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34462step0 raw34462step0Labels raw34462step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4341 node4341Labels := by rfl

def raw34463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw34463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34463step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34463step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34463step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34463 raw34463Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw34463 raw34463Labels = mixedMoment B raw34463step0 raw34463step0Labels := by
      have ha : raw34463step0 = (fun i j => raw34463 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34463step0 raw34463; decide +kernel
      have hl : raw34463step0Labels = raw34463Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34463 raw34463Labels permutation152 permutation3
    mixedMoment B raw34463step0 raw34463step0Labels = mixedMoment B raw34463step1 raw34463step1Labels := by
      have ha : raw34463step1 = raw34463step0 := by apply Matrix.ext; unfold raw34463step1 raw34463step0; decide +kernel
      have hl : raw34463step0Labels = labelEmbedding6 ∘ raw34463step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34463step0 raw34463step0Labels raw34463step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4939 node4939Labels := by rfl

def raw34464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw34464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw34464step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34464step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34464step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34464step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34464 raw34464Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw34464 raw34464Labels = mixedMoment B raw34464step0 raw34464step0Labels := by
      have hz : ∀ j, raw34464 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34464step0 = (fun i j => raw34464 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34464step0 raw34464; decide +kernel
      have hl : raw34464step0Labels = raw34464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34464 raw34464Labels permutation520 hz
    mixedMoment B raw34464step0 raw34464step0Labels = mixedMoment B raw34464step1 raw34464step1Labels := by
      have ha : raw34464step1 = (fun i j => raw34464step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34464step1 raw34464step0; decide +kernel
      have hl : raw34464step1Labels = raw34464step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34464step0 raw34464step0Labels permutation32 permutation3
    mixedMoment B raw34464step1 raw34464step1Labels = mixedMoment B raw34464step2 raw34464step2Labels := by
      have ha : raw34464step2 = raw34464step1 := by apply Matrix.ext; unfold raw34464step2 raw34464step1; decide +kernel
      have hl : raw34464step1Labels = labelEmbedding6 ∘ raw34464step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34464step1 raw34464step1Labels raw34464step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5168 node5168Labels := by rfl

def raw34465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34465step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34465step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34465step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34465step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34465step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34465 raw34465Labels = mixedMoment B node5227 node5227Labels := by
  calc
    mixedMoment B raw34465 raw34465Labels = mixedMoment B raw34465step0 raw34465step0Labels := by
      have ha : raw34465step0 = (fun i j => raw34465 (permutation283 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34465step0 raw34465; decide +kernel
      have hl : raw34465step0Labels = raw34465Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34465 raw34465Labels permutation283 permutation5
    mixedMoment B raw34465step0 raw34465step0Labels = mixedMoment B raw34465step1 raw34465step1Labels := by
      have ha : raw34465step1 = -raw34465step0 := by apply Matrix.ext; change ∀ i j, raw34465step1 i j = -(raw34465step0 i j); unfold raw34465step1 raw34465step0; decide +kernel
      have hl : raw34465step1Labels = raw34465step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34465step1 raw34465step1Labels = mixedMoment B raw34465step2 raw34465step2Labels := by
      have ha : raw34465step2 = raw34465step1 := by apply Matrix.ext; unfold raw34465step2 raw34465step1; decide +kernel
      have hl : raw34465step1Labels = labelEmbedding8 ∘ raw34465step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34465step1 raw34465step1Labels raw34465step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5227 node5227Labels := by rfl

def raw34466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw34466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34466step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34466 raw34466Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw34466 raw34466Labels = mixedMoment B raw34466step0 raw34466step0Labels := by
      have hz : ∀ j, raw34466 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34466step0 = (fun i j => raw34466 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34466step0 raw34466; decide +kernel
      have hl : raw34466step0Labels = raw34466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34466 raw34466Labels permutation520 hz
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw34467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw34467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw34467step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34467 raw34467Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw34467 raw34467Labels = mixedMoment B raw34467step0 raw34467step0Labels := by
      have ha : raw34467step0 = (fun i j => raw34467 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34467step0 raw34467; decide +kernel
      have hl : raw34467step0Labels = raw34467Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34467 raw34467Labels permutation170 permutation2
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw34468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34468step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34468step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34468step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34468step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34468 raw34468Labels = mixedMoment B node4601 node4601Labels := by
  calc
    mixedMoment B raw34468 raw34468Labels = mixedMoment B raw34468step0 raw34468step0Labels := by
      have ha : raw34468step0 = (fun i j => raw34468 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34468step0 raw34468; decide +kernel
      have hl : raw34468step0Labels = raw34468Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34468 raw34468Labels permutation170 permutation3
    mixedMoment B raw34468step0 raw34468step0Labels = mixedMoment B raw34468step1 raw34468step1Labels := by
      have ha : raw34468step1 = raw34468step0 := by apply Matrix.ext; unfold raw34468step1 raw34468step0; decide +kernel
      have hl : raw34468step0Labels = labelEmbedding6 ∘ raw34468step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34468step0 raw34468step0Labels raw34468step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4601 node4601Labels := by rfl

def raw34469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34469 raw34469Labels = mixedMoment B node4981 node4981Labels := by
  calc
    mixedMoment B raw34469 raw34469Labels = mixedMoment B raw34469step0 raw34469step0Labels := by
      have ha : raw34469step0 = (fun i j => raw34469 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34469step0 raw34469; decide +kernel
      have hl : raw34469step0Labels = raw34469Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34469 raw34469Labels permutation161 permutation2
    _ = mixedMoment B node4981 node4981Labels := by rfl

def raw34470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34470step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34470 raw34470Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw34470 raw34470Labels = mixedMoment B raw34470step0 raw34470step0Labels := by
      have hz : ∀ j, raw34470 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34470step0 = (fun i j => raw34470 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34470step0 raw34470; decide +kernel
      have hl : raw34470step0Labels = raw34470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34470 raw34470Labels permutation434 hz
    mixedMoment B raw34470step0 raw34470step0Labels = mixedMoment B raw34470step1 raw34470step1Labels := by
      have ha : raw34470step1 = (fun i j => raw34470step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34470step1 raw34470step0; decide +kernel
      have hl : raw34470step1Labels = raw34470step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34470step0 raw34470step0Labels permutation35 permutation2
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw34471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw34471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34471 raw34471Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw34471 raw34471Labels = mixedMoment B raw34471step0 raw34471step0Labels := by
      have hz : ∀ j, raw34471 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34471step0 = (fun i j => raw34471 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34471step0 raw34471; decide +kernel
      have hl : raw34471step0Labels = raw34471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34471 raw34471Labels permutation520 hz
    mixedMoment B raw34471step0 raw34471step0Labels = mixedMoment B raw34471step1 raw34471step1Labels := by
      have ha : raw34471step1 = (fun i j => raw34471step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34471step1 raw34471step0; decide +kernel
      have hl : raw34471step1Labels = raw34471step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34471step0 raw34471step0Labels permutation35 permutation2
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw34472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw34472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34472 raw34472Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw34472 raw34472Labels = mixedMoment B raw34472step0 raw34472step0Labels := by
      have ha : raw34472step0 = (fun i j => raw34472 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34472step0 raw34472; decide +kernel
      have hl : raw34472step0Labels = raw34472Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34472 raw34472Labels permutation173 permutation2
    _ = mixedMoment B node5192 node5192Labels := by rfl

def raw34473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw34473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34473 raw34473Labels = mixedMoment B node4981 node4981Labels := by
  calc
    mixedMoment B raw34473 raw34473Labels = mixedMoment B raw34473step0 raw34473step0Labels := by
      have ha : raw34473step0 = (fun i j => raw34473 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34473step0 raw34473; decide +kernel
      have hl : raw34473step0Labels = raw34473Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34473 raw34473Labels permutation155 permutation2
    _ = mixedMoment B node4981 node4981Labels := by rfl

def raw34474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw34474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw34474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34474step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34474step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34474 raw34474Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw34474 raw34474Labels = mixedMoment B raw34474step0 raw34474step0Labels := by
      have hz : ∀ j, raw34474 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34474step0 = (fun i j => raw34474 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34474step0 raw34474; decide +kernel
      have hl : raw34474step0Labels = raw34474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34474 raw34474Labels permutation520 hz
    mixedMoment B raw34474step0 raw34474step0Labels = mixedMoment B raw34474step1 raw34474step1Labels := by
      have ha : raw34474step1 = (fun i j => raw34474step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34474step1 raw34474step0; decide +kernel
      have hl : raw34474step1Labels = raw34474step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34474step0 raw34474step0Labels permutation33 permutation2
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw34475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw34475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34475 raw34475Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw34475 raw34475Labels = mixedMoment B raw34475step0 raw34475step0Labels := by
      have ha : raw34475step0 = (fun i j => raw34475 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34475step0 raw34475; decide +kernel
      have hl : raw34475step0Labels = raw34475Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34475 raw34475Labels permutation171 permutation2
    _ = mixedMoment B node5192 node5192Labels := by rfl

def raw34476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw34476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw34476step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34476 raw34476Labels = mixedMoment B node4981 node4981Labels := by
  calc
    mixedMoment B raw34476 raw34476Labels = mixedMoment B raw34476step0 raw34476step0Labels := by
      have ha : raw34476step0 = (fun i j => raw34476 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34476step0 raw34476; decide +kernel
      have hl : raw34476step0Labels = raw34476Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34476 raw34476Labels permutation153 permutation2
    _ = mixedMoment B node4981 node4981Labels := by rfl

def raw34477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw34477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw34477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34477 raw34477Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw34477 raw34477Labels = mixedMoment B raw34477step0 raw34477step0Labels := by
      have ha : raw34477step0 = (fun i j => raw34477 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34477step0 raw34477; decide +kernel
      have hl : raw34477step0Labels = raw34477Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34477 raw34477Labels permutation170 permutation2
    _ = mixedMoment B node5192 node5192Labels := by rfl

def raw34478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34478 raw34478Labels = mixedMoment B node5383 node5383Labels := by
  calc
    mixedMoment B raw34478 raw34478Labels = mixedMoment B raw34478step0 raw34478step0Labels := by
      have ha : raw34478step0 = (fun i j => raw34478 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34478step0 raw34478; decide +kernel
      have hl : raw34478step0Labels = raw34478Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34478 raw34478Labels permutation170 permutation2
    _ = mixedMoment B node5383 node5383Labels := by rfl

def raw34479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34479 raw34479Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw34479 raw34479Labels = mixedMoment B raw34479step0 raw34479step0Labels := by
      have ha : raw34479step0 = (fun i j => raw34479 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34479step0 raw34479; decide +kernel
      have hl : raw34479step0Labels = raw34479Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34479 raw34479Labels permutation156 permutation2
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw34480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34480 raw34480Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw34480 raw34480Labels = mixedMoment B raw34480step0 raw34480step0Labels := by
      have ha : raw34480step0 = (fun i j => raw34480 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34480step0 raw34480; decide +kernel
      have hl : raw34480step0Labels = raw34480Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34480 raw34480Labels permutation162 permutation2
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw34481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw34481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw34481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34481 raw34481Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw34481 raw34481Labels = mixedMoment B raw34481step0 raw34481step0Labels := by
      have ha : raw34481step0 = (fun i j => raw34481 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34481step0 raw34481; decide +kernel
      have hl : raw34481step0Labels = raw34481Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34481 raw34481Labels permutation168 permutation2
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw34482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw34482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34482step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34482 raw34482Labels = mixedMoment B node5427 node5427Labels := by
  calc
    mixedMoment B raw34482 raw34482Labels = mixedMoment B raw34482step0 raw34482step0Labels := by
      have ha : raw34482step0 = (fun i j => raw34482 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34482step0 raw34482; decide +kernel
      have hl : raw34482step0Labels = raw34482Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34482 raw34482Labels permutation170 permutation2
    _ = mixedMoment B node5427 node5427Labels := by rfl

def raw34483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34483step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34483step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34483step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34483 raw34483Labels = mixedMoment B node4618 node4618Labels := by
  calc
    mixedMoment B raw34483 raw34483Labels = mixedMoment B raw34483step0 raw34483step0Labels := by
      have hz : ∀ j, raw34483 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw34483step0 = (fun i j => raw34483 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw34483step0 raw34483; decide +kernel
      have hl : raw34483step0Labels = raw34483Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34483 raw34483Labels permutation265 hz
    mixedMoment B raw34483step0 raw34483step0Labels = mixedMoment B raw34483step1 raw34483step1Labels := by
      have ha : raw34483step1 = (fun i j => raw34483step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34483step1 raw34483step0; decide +kernel
      have hl : raw34483step1Labels = raw34483step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34483step0 raw34483step0Labels permutation50 permutation2
    _ = mixedMoment B node4618 node4618Labels := by rfl

def raw34484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34484 raw34484Labels = mixedMoment B node4964 node4964Labels := by
  calc
    mixedMoment B raw34484 raw34484Labels = mixedMoment B raw34484step0 raw34484step0Labels := by
      have ha : raw34484step0 = (fun i j => raw34484 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34484step0 raw34484; decide +kernel
      have hl : raw34484step0Labels = raw34484Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34484 raw34484Labels permutation173 permutation2
    _ = mixedMoment B node4964 node4964Labels := by rfl

def raw34485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34485 raw34485Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw34485 raw34485Labels = mixedMoment B raw34485step0 raw34485step0Labels := by
      have ha : raw34485step0 = (fun i j => raw34485 (permutation163 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34485step0 raw34485; decide +kernel
      have hl : raw34485step0Labels = raw34485Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34485 raw34485Labels permutation163 permutation2
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw34486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw34486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34486step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34486 raw34486Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw34486 raw34486Labels = mixedMoment B raw34486step0 raw34486step0Labels := by
      have ha : raw34486step0 = (fun i j => raw34486 (permutation169 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34486step0 raw34486; decide +kernel
      have hl : raw34486step0Labels = raw34486Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34486 raw34486Labels permutation169 permutation2
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw34487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw34487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34487step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34487 raw34487Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw34487 raw34487Labels = mixedMoment B raw34487step0 raw34487step0Labels := by
      have ha : raw34487step0 = (fun i j => raw34487 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34487step0 raw34487; decide +kernel
      have hl : raw34487step0Labels = raw34487Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34487 raw34487Labels permutation173 permutation2
    _ = mixedMoment B node5137 node5137Labels := by rfl

def raw34488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34488step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34488 raw34488Labels = mixedMoment B node4964 node4964Labels := by
  calc
    mixedMoment B raw34488 raw34488Labels = mixedMoment B raw34488step0 raw34488step0Labels := by
      have ha : raw34488step0 = (fun i j => raw34488 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34488step0 raw34488; decide +kernel
      have hl : raw34488step0Labels = raw34488Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34488 raw34488Labels permutation171 permutation2
    _ = mixedMoment B node4964 node4964Labels := by rfl

def raw34489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34489step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34489 raw34489Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw34489 raw34489Labels = mixedMoment B raw34489step0 raw34489step0Labels := by
      have ha : raw34489step0 = (fun i j => raw34489 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34489step0 raw34489; decide +kernel
      have hl : raw34489step0Labels = raw34489Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34489 raw34489Labels permutation157 permutation2
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw34490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw34490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34490step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34490 raw34490Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw34490 raw34490Labels = mixedMoment B raw34490step0 raw34490step0Labels := by
      have ha : raw34490step0 = (fun i j => raw34490 (permutation168 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34490step0 raw34490; decide +kernel
      have hl : raw34490step0Labels = raw34490Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34490 raw34490Labels permutation168 permutation2
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw34491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw34491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34491step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34491 raw34491Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw34491 raw34491Labels = mixedMoment B raw34491step0 raw34491step0Labels := by
      have ha : raw34491step0 = (fun i j => raw34491 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34491step0 raw34491; decide +kernel
      have hl : raw34491step0Labels = raw34491Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34491 raw34491Labels permutation171 permutation2
    _ = mixedMoment B node5137 node5137Labels := by rfl

def raw34492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw34492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34492step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34492step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34492 raw34492Labels = mixedMoment B node4964 node4964Labels := by
  calc
    mixedMoment B raw34492 raw34492Labels = mixedMoment B raw34492step0 raw34492step0Labels := by
      have ha : raw34492step0 = (fun i j => raw34492 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34492step0 raw34492; decide +kernel
      have hl : raw34492step0Labels = raw34492Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34492 raw34492Labels permutation170 permutation2
    _ = mixedMoment B node4964 node4964Labels := by rfl

def raw34493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw34493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34493step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34493 raw34493Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw34493 raw34493Labels = mixedMoment B raw34493step0 raw34493step0Labels := by
      have ha : raw34493step0 = (fun i j => raw34493 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34493step0 raw34493; decide +kernel
      have hl : raw34493step0Labels = raw34493Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34493 raw34493Labels permutation156 permutation2
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw34494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw34494Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw34494step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34494 raw34494Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw34494 raw34494Labels = mixedMoment B raw34494step0 raw34494step0Labels := by
      have ha : raw34494step0 = (fun i j => raw34494 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34494step0 raw34494; decide +kernel
      have hl : raw34494step0Labels = raw34494Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34494 raw34494Labels permutation162 permutation2
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw34495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw34495Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw34495step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34495 raw34495Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw34495 raw34495Labels = mixedMoment B raw34495step0 raw34495step0Labels := by
      have ha : raw34495step0 = (fun i j => raw34495 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34495step0 raw34495; decide +kernel
      have hl : raw34495step0Labels = raw34495Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34495 raw34495Labels permutation170 permutation2
    _ = mixedMoment B node5137 node5137Labels := by rfl

def raw34496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34496Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34496 raw34496Labels = mixedMoment B node4975 node4975Labels := by
  calc
    _ = mixedMoment B node4975 node4975Labels := by rfl

def raw34497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw34497Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34497step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34497 raw34497Labels = mixedMoment B node5150 node5150Labels := by
  calc
    mixedMoment B raw34497 raw34497Labels = mixedMoment B raw34497step0 raw34497step0Labels := by
      have ha : raw34497step0 = (fun i j => raw34497 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34497step0 raw34497; decide +kernel
      have hl : raw34497step0Labels = raw34497Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34497 raw34497Labels permutation164 permutation2
    _ = mixedMoment B node5150 node5150Labels := by rfl

def raw34498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34498Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34498step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34498step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34498step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34498 raw34498Labels = mixedMoment B node3867 node3867Labels := by
  calc
    mixedMoment B raw34498 raw34498Labels = mixedMoment B raw34498step0 raw34498step0Labels := by
      have ha : raw34498step0 = (fun i j => raw34498 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34498step0 raw34498; decide +kernel
      have hl : raw34498step0Labels = raw34498Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34498 raw34498Labels permutation246 permutation7
    mixedMoment B raw34498step0 raw34498step0Labels = mixedMoment B raw34498step1 raw34498step1Labels := by
      have ha : raw34498step1 = -raw34498step0 := by apply Matrix.ext; change ∀ i j, raw34498step1 i j = -(raw34498step0 i j); unfold raw34498step1 raw34498step0; decide +kernel
      have hl : raw34498step1Labels = raw34498step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34498step1 raw34498step1Labels = mixedMoment B raw34498step2 raw34498step2Labels := by
      have ha : raw34498step2 = raw34498step1 := by apply Matrix.ext; unfold raw34498step2 raw34498step1; decide +kernel
      have hl : raw34498step1Labels = labelEmbedding1 ∘ raw34498step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34498step1 raw34498step1Labels raw34498step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3867 node3867Labels := by rfl

def raw34499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34499Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw34499step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34499step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34499step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34499step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34499step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34499 raw34499Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw34499 raw34499Labels = mixedMoment B raw34499step0 raw34499step0Labels := by
      have ha : raw34499step0 = (fun i j => raw34499 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34499step0 raw34499; decide +kernel
      have hl : raw34499step0Labels = raw34499Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34499 raw34499Labels permutation246 permutation7
    mixedMoment B raw34499step0 raw34499step0Labels = mixedMoment B raw34499step1 raw34499step1Labels := by
      have ha : raw34499step1 = -raw34499step0 := by apply Matrix.ext; change ∀ i j, raw34499step1 i j = -(raw34499step0 i j); unfold raw34499step1 raw34499step0; decide +kernel
      have hl : raw34499step1Labels = raw34499step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34499step1 raw34499step1Labels = mixedMoment B raw34499step2 raw34499step2Labels := by
      have ha : raw34499step2 = raw34499step1 := by apply Matrix.ext; unfold raw34499step2 raw34499step1; decide +kernel
      have hl : raw34499step1Labels = labelEmbedding1 ∘ raw34499step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34499step1 raw34499step1Labels raw34499step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw34500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34500Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw34500step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34500step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34500step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34500 raw34500Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw34500 raw34500Labels = mixedMoment B raw34500step0 raw34500step0Labels := by
      have ha : raw34500step0 = (fun i j => raw34500 (permutation248 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34500step0 raw34500; decide +kernel
      have hl : raw34500step0Labels = raw34500Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34500 raw34500Labels permutation248 permutation7
    mixedMoment B raw34500step0 raw34500step0Labels = mixedMoment B raw34500step1 raw34500step1Labels := by
      have ha : raw34500step1 = -raw34500step0 := by apply Matrix.ext; change ∀ i j, raw34500step1 i j = -(raw34500step0 i j); unfold raw34500step1 raw34500step0; decide +kernel
      have hl : raw34500step1Labels = raw34500step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34500step1 raw34500step1Labels = mixedMoment B raw34500step2 raw34500step2Labels := by
      have ha : raw34500step2 = raw34500step1 := by apply Matrix.ext; unfold raw34500step2 raw34500step1; decide +kernel
      have hl : raw34500step1Labels = labelEmbedding1 ∘ raw34500step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34500step1 raw34500step1Labels raw34500step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw34501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw34501Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw34501step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34501step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34501step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34501step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34501step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34501 raw34501Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw34501 raw34501Labels = mixedMoment B raw34501step0 raw34501step0Labels := by
      have ha : raw34501step0 = (fun i j => raw34501 (permutation250 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34501step0 raw34501; decide +kernel
      have hl : raw34501step0Labels = raw34501Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34501 raw34501Labels permutation250 permutation7
    mixedMoment B raw34501step0 raw34501step0Labels = mixedMoment B raw34501step1 raw34501step1Labels := by
      have ha : raw34501step1 = -raw34501step0 := by apply Matrix.ext; change ∀ i j, raw34501step1 i j = -(raw34501step0 i j); unfold raw34501step1 raw34501step0; decide +kernel
      have hl : raw34501step1Labels = raw34501step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34501step1 raw34501step1Labels = mixedMoment B raw34501step2 raw34501step2Labels := by
      have ha : raw34501step2 = raw34501step1 := by apply Matrix.ext; unfold raw34501step2 raw34501step1; decide +kernel
      have hl : raw34501step1Labels = labelEmbedding1 ∘ raw34501step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34501step1 raw34501step1Labels raw34501step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw34502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw34502Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34502step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34502step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34502step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34502step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34502step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34502 raw34502Labels = mixedMoment B node3844 node3844Labels := by
  calc
    mixedMoment B raw34502 raw34502Labels = mixedMoment B raw34502step0 raw34502step0Labels := by
      have ha : raw34502step0 = (fun i j => raw34502 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34502step0 raw34502; decide +kernel
      have hl : raw34502step0Labels = raw34502Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34502 raw34502Labels permutation246 permutation7
    mixedMoment B raw34502step0 raw34502step0Labels = mixedMoment B raw34502step1 raw34502step1Labels := by
      have ha : raw34502step1 = -raw34502step0 := by apply Matrix.ext; change ∀ i j, raw34502step1 i j = -(raw34502step0 i j); unfold raw34502step1 raw34502step0; decide +kernel
      have hl : raw34502step1Labels = raw34502step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34502step1 raw34502step1Labels = mixedMoment B raw34502step2 raw34502step2Labels := by
      have ha : raw34502step2 = raw34502step1 := by apply Matrix.ext; unfold raw34502step2 raw34502step1; decide +kernel
      have hl : raw34502step1Labels = labelEmbedding1 ∘ raw34502step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34502step1 raw34502step1Labels raw34502step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3844 node3844Labels := by rfl

def raw34503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34503Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34503step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34503step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34503step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34503step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34503step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34503step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34503 raw34503Labels = mixedMoment B node3304 node3304Labels := by
  calc
    mixedMoment B raw34503 raw34503Labels = mixedMoment B raw34503step0 raw34503step0Labels := by
      have hz : ∀ j, raw34503 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw34503step0 = (fun i j => raw34503 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw34503step0 raw34503; decide +kernel
      have hl : raw34503step0Labels = raw34503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34503 raw34503Labels permutation265 hz
    mixedMoment B raw34503step0 raw34503step0Labels = mixedMoment B raw34503step1 raw34503step1Labels := by
      have ha : raw34503step1 = (fun i j => raw34503step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34503step1 raw34503step0; decide +kernel
      have hl : raw34503step1Labels = raw34503step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34503step0 raw34503step0Labels permutation50 permutation7
    mixedMoment B raw34503step1 raw34503step1Labels = mixedMoment B raw34503step2 raw34503step2Labels := by
      have ha : raw34503step2 = -raw34503step1 := by apply Matrix.ext; change ∀ i j, raw34503step2 i j = -(raw34503step1 i j); unfold raw34503step2 raw34503step1; decide +kernel
      have hl : raw34503step2Labels = raw34503step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34503step2 raw34503step2Labels = mixedMoment B raw34503step3 raw34503step3Labels := by
      have ha : raw34503step3 = raw34503step2 := by apply Matrix.ext; unfold raw34503step3 raw34503step2; decide +kernel
      have hl : raw34503step2Labels = labelEmbedding1 ∘ raw34503step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34503step2 raw34503step2Labels raw34503step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3304 node3304Labels := by rfl

def raw34504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34504Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34504step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34504step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34504step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34504step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34504 raw34504Labels = mixedMoment B node3554 node3554Labels := by
  calc
    mixedMoment B raw34504 raw34504Labels = mixedMoment B raw34504step0 raw34504step0Labels := by
      have ha : raw34504step0 = (fun i j => raw34504 (permutation249 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34504step0 raw34504; decide +kernel
      have hl : raw34504step0Labels = raw34504Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34504 raw34504Labels permutation249 permutation7
    mixedMoment B raw34504step0 raw34504step0Labels = mixedMoment B raw34504step1 raw34504step1Labels := by
      have ha : raw34504step1 = -raw34504step0 := by apply Matrix.ext; change ∀ i j, raw34504step1 i j = -(raw34504step0 i j); unfold raw34504step1 raw34504step0; decide +kernel
      have hl : raw34504step1Labels = raw34504step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34504step1 raw34504step1Labels = mixedMoment B raw34504step2 raw34504step2Labels := by
      have ha : raw34504step2 = raw34504step1 := by apply Matrix.ext; unfold raw34504step2 raw34504step1; decide +kernel
      have hl : raw34504step1Labels = labelEmbedding1 ∘ raw34504step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34504step1 raw34504step1Labels raw34504step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3554 node3554Labels := by rfl

def raw34505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34505Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34505step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34505step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34505step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34505step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34505step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34505 raw34505Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw34505 raw34505Labels = mixedMoment B raw34505step0 raw34505step0Labels := by
      have ha : raw34505step0 = (fun i j => raw34505 (permutation249 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34505step0 raw34505; decide +kernel
      have hl : raw34505step0Labels = raw34505Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34505 raw34505Labels permutation249 permutation7
    mixedMoment B raw34505step0 raw34505step0Labels = mixedMoment B raw34505step1 raw34505step1Labels := by
      have ha : raw34505step1 = -raw34505step0 := by apply Matrix.ext; change ∀ i j, raw34505step1 i j = -(raw34505step0 i j); unfold raw34505step1 raw34505step0; decide +kernel
      have hl : raw34505step1Labels = raw34505step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34505step1 raw34505step1Labels = mixedMoment B raw34505step2 raw34505step2Labels := by
      have ha : raw34505step2 = raw34505step1 := by apply Matrix.ext; unfold raw34505step2 raw34505step1; decide +kernel
      have hl : raw34505step1Labels = labelEmbedding1 ∘ raw34505step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34505step1 raw34505step1Labels raw34505step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

def raw34506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw34506Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34506step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34506step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34506step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34506step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34506step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34506 raw34506Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw34506 raw34506Labels = mixedMoment B raw34506step0 raw34506step0Labels := by
      have ha : raw34506step0 = (fun i j => raw34506 (permutation251 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34506step0 raw34506; decide +kernel
      have hl : raw34506step0Labels = raw34506Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34506 raw34506Labels permutation251 permutation7
    mixedMoment B raw34506step0 raw34506step0Labels = mixedMoment B raw34506step1 raw34506step1Labels := by
      have ha : raw34506step1 = -raw34506step0 := by apply Matrix.ext; change ∀ i j, raw34506step1 i j = -(raw34506step0 i j); unfold raw34506step1 raw34506step0; decide +kernel
      have hl : raw34506step1Labels = raw34506step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34506step1 raw34506step1Labels = mixedMoment B raw34506step2 raw34506step2Labels := by
      have ha : raw34506step2 = raw34506step1 := by apply Matrix.ext; unfold raw34506step2 raw34506step1; decide +kernel
      have hl : raw34506step1Labels = labelEmbedding1 ∘ raw34506step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34506step1 raw34506step1Labels raw34506step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

def raw34507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw34507Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34507step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34507step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34507step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34507step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34507 raw34507Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw34507 raw34507Labels = mixedMoment B raw34507step0 raw34507step0Labels := by
      have ha : raw34507step0 = (fun i j => raw34507 (permutation249 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34507step0 raw34507; decide +kernel
      have hl : raw34507step0Labels = raw34507Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34507 raw34507Labels permutation249 permutation7
    mixedMoment B raw34507step0 raw34507step0Labels = mixedMoment B raw34507step1 raw34507step1Labels := by
      have ha : raw34507step1 = -raw34507step0 := by apply Matrix.ext; change ∀ i j, raw34507step1 i j = -(raw34507step0 i j); unfold raw34507step1 raw34507step0; decide +kernel
      have hl : raw34507step1Labels = raw34507step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34507step1 raw34507step1Labels = mixedMoment B raw34507step2 raw34507step2Labels := by
      have ha : raw34507step2 = raw34507step1 := by apply Matrix.ext; unfold raw34507step2 raw34507step1; decide +kernel
      have hl : raw34507step1Labels = labelEmbedding1 ∘ raw34507step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34507step1 raw34507step1Labels raw34507step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

def raw34508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34508Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34508step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34508step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34508step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34508 raw34508Labels = mixedMoment B node3554 node3554Labels := by
  calc
    mixedMoment B raw34508 raw34508Labels = mixedMoment B raw34508step0 raw34508step0Labels := by
      have ha : raw34508step0 = (fun i j => raw34508 (permutation247 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34508step0 raw34508; decide +kernel
      have hl : raw34508step0Labels = raw34508Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34508 raw34508Labels permutation247 permutation7
    mixedMoment B raw34508step0 raw34508step0Labels = mixedMoment B raw34508step1 raw34508step1Labels := by
      have ha : raw34508step1 = -raw34508step0 := by apply Matrix.ext; change ∀ i j, raw34508step1 i j = -(raw34508step0 i j); unfold raw34508step1 raw34508step0; decide +kernel
      have hl : raw34508step1Labels = raw34508step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34508step1 raw34508step1Labels = mixedMoment B raw34508step2 raw34508step2Labels := by
      have ha : raw34508step2 = raw34508step1 := by apply Matrix.ext; unfold raw34508step2 raw34508step1; decide +kernel
      have hl : raw34508step1Labels = labelEmbedding1 ∘ raw34508step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34508step1 raw34508step1Labels raw34508step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3554 node3554Labels := by rfl

def raw34509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw34509Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34509step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34509step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34509step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34509step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34509step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34509 raw34509Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw34509 raw34509Labels = mixedMoment B raw34509step0 raw34509step0Labels := by
      have ha : raw34509step0 = (fun i j => raw34509 (permutation247 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34509step0 raw34509; decide +kernel
      have hl : raw34509step0Labels = raw34509Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34509 raw34509Labels permutation247 permutation7
    mixedMoment B raw34509step0 raw34509step0Labels = mixedMoment B raw34509step1 raw34509step1Labels := by
      have ha : raw34509step1 = -raw34509step0 := by apply Matrix.ext; change ∀ i j, raw34509step1 i j = -(raw34509step0 i j); unfold raw34509step1 raw34509step0; decide +kernel
      have hl : raw34509step1Labels = raw34509step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34509step1 raw34509step1Labels = mixedMoment B raw34509step2 raw34509step2Labels := by
      have ha : raw34509step2 = raw34509step1 := by apply Matrix.ext; unfold raw34509step2 raw34509step1; decide +kernel
      have hl : raw34509step1Labels = labelEmbedding1 ∘ raw34509step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34509step1 raw34509step1Labels raw34509step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

def raw34510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw34510Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34510step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34510step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34510step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34510step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34510step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34510 raw34510Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw34510 raw34510Labels = mixedMoment B raw34510step0 raw34510step0Labels := by
      have ha : raw34510step0 = (fun i j => raw34510 (permutation250 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34510step0 raw34510; decide +kernel
      have hl : raw34510step0Labels = raw34510Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34510 raw34510Labels permutation250 permutation7
    mixedMoment B raw34510step0 raw34510step0Labels = mixedMoment B raw34510step1 raw34510step1Labels := by
      have ha : raw34510step1 = -raw34510step0 := by apply Matrix.ext; change ∀ i j, raw34510step1 i j = -(raw34510step0 i j); unfold raw34510step1 raw34510step0; decide +kernel
      have hl : raw34510step1Labels = raw34510step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34510step1 raw34510step1Labels = mixedMoment B raw34510step2 raw34510step2Labels := by
      have ha : raw34510step2 = raw34510step1 := by apply Matrix.ext; unfold raw34510step2 raw34510step1; decide +kernel
      have hl : raw34510step1Labels = labelEmbedding1 ∘ raw34510step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34510step1 raw34510step1Labels raw34510step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

def raw34511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw34511Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34511step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34511step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34511step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34511step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34511step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34511 raw34511Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw34511 raw34511Labels = mixedMoment B raw34511step0 raw34511step0Labels := by
      have ha : raw34511step0 = (fun i j => raw34511 (permutation247 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34511step0 raw34511; decide +kernel
      have hl : raw34511step0Labels = raw34511Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34511 raw34511Labels permutation247 permutation7
    mixedMoment B raw34511step0 raw34511step0Labels = mixedMoment B raw34511step1 raw34511step1Labels := by
      have ha : raw34511step1 = -raw34511step0 := by apply Matrix.ext; change ∀ i j, raw34511step1 i j = -(raw34511step0 i j); unfold raw34511step1 raw34511step0; decide +kernel
      have hl : raw34511step1Labels = raw34511step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34511step1 raw34511step1Labels = mixedMoment B raw34511step2 raw34511step2Labels := by
      have ha : raw34511step2 = raw34511step1 := by apply Matrix.ext; unfold raw34511step2 raw34511step1; decide +kernel
      have hl : raw34511step1Labels = labelEmbedding1 ∘ raw34511step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34511step1 raw34511step1Labels raw34511step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

def raw34512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw34512Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34512step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34512step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34512step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34512step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34512 raw34512Labels = mixedMoment B node3554 node3554Labels := by
  calc
    mixedMoment B raw34512 raw34512Labels = mixedMoment B raw34512step0 raw34512step0Labels := by
      have ha : raw34512step0 = (fun i j => raw34512 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34512step0 raw34512; decide +kernel
      have hl : raw34512step0Labels = raw34512Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34512 raw34512Labels permutation246 permutation7
    mixedMoment B raw34512step0 raw34512step0Labels = mixedMoment B raw34512step1 raw34512step1Labels := by
      have ha : raw34512step1 = -raw34512step0 := by apply Matrix.ext; change ∀ i j, raw34512step1 i j = -(raw34512step0 i j); unfold raw34512step1 raw34512step0; decide +kernel
      have hl : raw34512step1Labels = raw34512step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34512step1 raw34512step1Labels = mixedMoment B raw34512step2 raw34512step2Labels := by
      have ha : raw34512step2 = raw34512step1 := by apply Matrix.ext; unfold raw34512step2 raw34512step1; decide +kernel
      have hl : raw34512step1Labels = labelEmbedding1 ∘ raw34512step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34512step1 raw34512step1Labels raw34512step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3554 node3554Labels := by rfl

def raw34513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw34513Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34513step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34513step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34513step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34513step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34513 raw34513Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw34513 raw34513Labels = mixedMoment B raw34513step0 raw34513step0Labels := by
      have ha : raw34513step0 = (fun i j => raw34513 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34513step0 raw34513; decide +kernel
      have hl : raw34513step0Labels = raw34513Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34513 raw34513Labels permutation246 permutation7
    mixedMoment B raw34513step0 raw34513step0Labels = mixedMoment B raw34513step1 raw34513step1Labels := by
      have ha : raw34513step1 = -raw34513step0 := by apply Matrix.ext; change ∀ i j, raw34513step1 i j = -(raw34513step0 i j); unfold raw34513step1 raw34513step0; decide +kernel
      have hl : raw34513step1Labels = raw34513step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34513step1 raw34513step1Labels = mixedMoment B raw34513step2 raw34513step2Labels := by
      have ha : raw34513step2 = raw34513step1 := by apply Matrix.ext; unfold raw34513step2 raw34513step1; decide +kernel
      have hl : raw34513step1Labels = labelEmbedding1 ∘ raw34513step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34513step1 raw34513step1Labels raw34513step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

def raw34514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw34514Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw34514step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34514step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34514step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34514step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34514 raw34514Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw34514 raw34514Labels = mixedMoment B raw34514step0 raw34514step0Labels := by
      have ha : raw34514step0 = (fun i j => raw34514 (permutation248 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34514step0 raw34514; decide +kernel
      have hl : raw34514step0Labels = raw34514Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34514 raw34514Labels permutation248 permutation7
    mixedMoment B raw34514step0 raw34514step0Labels = mixedMoment B raw34514step1 raw34514step1Labels := by
      have ha : raw34514step1 = -raw34514step0 := by apply Matrix.ext; change ∀ i j, raw34514step1 i j = -(raw34514step0 i j); unfold raw34514step1 raw34514step0; decide +kernel
      have hl : raw34514step1Labels = raw34514step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34514step1 raw34514step1Labels = mixedMoment B raw34514step2 raw34514step2Labels := by
      have ha : raw34514step2 = raw34514step1 := by apply Matrix.ext; unfold raw34514step2 raw34514step1; decide +kernel
      have hl : raw34514step1Labels = labelEmbedding1 ∘ raw34514step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34514step1 raw34514step1Labels raw34514step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

def raw34515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw34515Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw34515step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34515step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34515step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34515step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34515step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34515 raw34515Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw34515 raw34515Labels = mixedMoment B raw34515step0 raw34515step0Labels := by
      have ha : raw34515step0 = (fun i j => raw34515 (permutation246 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34515step0 raw34515; decide +kernel
      have hl : raw34515step0Labels = raw34515Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34515 raw34515Labels permutation246 permutation7
    mixedMoment B raw34515step0 raw34515step0Labels = mixedMoment B raw34515step1 raw34515step1Labels := by
      have ha : raw34515step1 = -raw34515step0 := by apply Matrix.ext; change ∀ i j, raw34515step1 i j = -(raw34515step0 i j); unfold raw34515step1 raw34515step0; decide +kernel
      have hl : raw34515step1Labels = raw34515step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34515step1 raw34515step1Labels = mixedMoment B raw34515step2 raw34515step2Labels := by
      have ha : raw34515step2 = raw34515step1 := by apply Matrix.ext; unfold raw34515step2 raw34515step1; decide +kernel
      have hl : raw34515step1Labels = labelEmbedding1 ∘ raw34515step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34515step1 raw34515step1Labels raw34515step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

def raw34516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw34516Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw34516step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw34516step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34516 raw34516Labels = mixedMoment B node2690 node2690Labels := by
  calc
    mixedMoment B raw34516 raw34516Labels = mixedMoment B raw34516step0 raw34516step0Labels := by
      have ha : raw34516step0 = (fun i j => raw34516 (permutation639 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34516step0 raw34516; decide +kernel
      have hl : raw34516step0Labels = raw34516Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34516 raw34516Labels permutation639 permutation5
    mixedMoment B raw34516step0 raw34516step0Labels = mixedMoment B raw34516step1 raw34516step1Labels := by
      have ha : raw34516step1 = raw34516step0 := by apply Matrix.ext; unfold raw34516step1 raw34516step0; decide +kernel
      have hl : raw34516step0Labels = labelEmbedding1 ∘ raw34516step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34516step0 raw34516step0Labels raw34516step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2690 node2690Labels := by rfl

def raw34517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw34517Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw34517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw34517step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw34517step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw34517step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34517 raw34517Labels = mixedMoment B node2700 node2700Labels := by
  calc
    mixedMoment B raw34517 raw34517Labels = mixedMoment B raw34517step0 raw34517step0Labels := by
      have ha : raw34517step0 = (fun i j => raw34517 (permutation640 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34517step0 raw34517; decide +kernel
      have hl : raw34517step0Labels = raw34517Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34517 raw34517Labels permutation640 permutation5
    mixedMoment B raw34517step0 raw34517step0Labels = mixedMoment B raw34517step1 raw34517step1Labels := by
      have ha : raw34517step1 = raw34517step0 := by apply Matrix.ext; unfold raw34517step1 raw34517step0; decide +kernel
      have hl : raw34517step0Labels = labelEmbedding1 ∘ raw34517step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34517step0 raw34517step0Labels raw34517step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2700 node2700Labels := by rfl

def raw34518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34518step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34518step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34518 raw34518Labels = mixedMoment B node4337 node4337Labels := by
  calc
    mixedMoment B raw34518 raw34518Labels = mixedMoment B raw34518step0 raw34518step0Labels := by
      have ha : raw34518step0 = (fun i j => raw34518 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34518step0 raw34518; decide +kernel
      have hl : raw34518step0Labels = raw34518Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34518 raw34518Labels permutation173 permutation3
    mixedMoment B raw34518step0 raw34518step0Labels = mixedMoment B raw34518step1 raw34518step1Labels := by
      have ha : raw34518step1 = raw34518step0 := by apply Matrix.ext; unfold raw34518step1 raw34518step0; decide +kernel
      have hl : raw34518step0Labels = labelEmbedding6 ∘ raw34518step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34518step0 raw34518step0Labels raw34518step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4337 node4337Labels := by rfl

def raw34519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34519step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34519step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34519step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34519 raw34519Labels = mixedMoment B node4936 node4936Labels := by
  calc
    mixedMoment B raw34519 raw34519Labels = mixedMoment B raw34519step0 raw34519step0Labels := by
      have ha : raw34519step0 = (fun i j => raw34519 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34519step0 raw34519; decide +kernel
      have hl : raw34519step0Labels = raw34519Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34519 raw34519Labels permutation173 permutation3
    mixedMoment B raw34519step0 raw34519step0Labels = mixedMoment B raw34519step1 raw34519step1Labels := by
      have ha : raw34519step1 = raw34519step0 := by apply Matrix.ext; unfold raw34519step1 raw34519step0; decide +kernel
      have hl : raw34519step0Labels = labelEmbedding6 ∘ raw34519step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34519step0 raw34519step0Labels raw34519step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4936 node4936Labels := by rfl

def raw34520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34520step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34520step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34520step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34520step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34520 raw34520Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw34520 raw34520Labels = mixedMoment B raw34520step0 raw34520step0Labels := by
      have hz : ∀ j, raw34520 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34520step0 = (fun i j => raw34520 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34520step0 raw34520; decide +kernel
      have hl : raw34520step0Labels = raw34520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34520 raw34520Labels permutation434 hz
    mixedMoment B raw34520step0 raw34520step0Labels = mixedMoment B raw34520step1 raw34520step1Labels := by
      have ha : raw34520step1 = (fun i j => raw34520step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34520step1 raw34520step0; decide +kernel
      have hl : raw34520step1Labels = raw34520step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34520step0 raw34520step0Labels permutation37 permutation3
    mixedMoment B raw34520step1 raw34520step1Labels = mixedMoment B raw34520step2 raw34520step2Labels := by
      have ha : raw34520step2 = raw34520step1 := by apply Matrix.ext; unfold raw34520step2 raw34520step1; decide +kernel
      have hl : raw34520step1Labels = labelEmbedding6 ∘ raw34520step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34520step1 raw34520step1Labels raw34520step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw34521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw34521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34521step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34521step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34521 raw34521Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw34521 raw34521Labels = mixedMoment B raw34521step0 raw34521step0Labels := by
      have hz : ∀ j, raw34521 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34521step0 = (fun i j => raw34521 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34521step0 raw34521; decide +kernel
      have hl : raw34521step0Labels = raw34521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34521 raw34521Labels permutation520 hz
    mixedMoment B raw34521step0 raw34521step0Labels = mixedMoment B raw34521step1 raw34521step1Labels := by
      have ha : raw34521step1 = (fun i j => raw34521step0 (permutation37 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34521step1 raw34521step0; decide +kernel
      have hl : raw34521step1Labels = raw34521step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34521step0 raw34521step0Labels permutation37 permutation3
    mixedMoment B raw34521step1 raw34521step1Labels = mixedMoment B raw34521step2 raw34521step2Labels := by
      have ha : raw34521step2 = raw34521step1 := by apply Matrix.ext; unfold raw34521step2 raw34521step1; decide +kernel
      have hl : raw34521step1Labels = labelEmbedding6 ∘ raw34521step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34521step1 raw34521step1Labels raw34521step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw34522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw34522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34522step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34522step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34522 raw34522Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw34522 raw34522Labels = mixedMoment B raw34522step0 raw34522step0Labels := by
      have ha : raw34522step0 = (fun i j => raw34522 (permutation173 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34522step0 raw34522; decide +kernel
      have hl : raw34522step0Labels = raw34522Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34522 raw34522Labels permutation173 permutation3
    mixedMoment B raw34522step0 raw34522step0Labels = mixedMoment B raw34522step1 raw34522step1Labels := by
      have ha : raw34522step1 = raw34522step0 := by apply Matrix.ext; unfold raw34522step1 raw34522step0; decide +kernel
      have hl : raw34522step0Labels = labelEmbedding6 ∘ raw34522step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34522step0 raw34522step0Labels raw34522step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

def raw34523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34523step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34523step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34523step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34523 raw34523Labels = mixedMoment B node4337 node4337Labels := by
  calc
    mixedMoment B raw34523 raw34523Labels = mixedMoment B raw34523step0 raw34523step0Labels := by
      have ha : raw34523step0 = (fun i j => raw34523 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34523step0 raw34523; decide +kernel
      have hl : raw34523step0Labels = raw34523Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34523 raw34523Labels permutation171 permutation3
    mixedMoment B raw34523step0 raw34523step0Labels = mixedMoment B raw34523step1 raw34523step1Labels := by
      have ha : raw34523step1 = raw34523step0 := by apply Matrix.ext; unfold raw34523step1 raw34523step0; decide +kernel
      have hl : raw34523step0Labels = labelEmbedding6 ∘ raw34523step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34523step0 raw34523step0Labels raw34523step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4337 node4337Labels := by rfl

def raw34524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34524step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34524step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34524step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34524 raw34524Labels = mixedMoment B node4936 node4936Labels := by
  calc
    mixedMoment B raw34524 raw34524Labels = mixedMoment B raw34524step0 raw34524step0Labels := by
      have ha : raw34524step0 = (fun i j => raw34524 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34524step0 raw34524; decide +kernel
      have hl : raw34524step0Labels = raw34524Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34524 raw34524Labels permutation171 permutation3
    mixedMoment B raw34524step0 raw34524step0Labels = mixedMoment B raw34524step1 raw34524step1Labels := by
      have ha : raw34524step1 = raw34524step0 := by apply Matrix.ext; unfold raw34524step1 raw34524step0; decide +kernel
      have hl : raw34524step0Labels = labelEmbedding6 ∘ raw34524step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34524step0 raw34524step0Labels raw34524step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4936 node4936Labels := by rfl

def raw34525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw34525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34525step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34525step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34525step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34525step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34525 raw34525Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw34525 raw34525Labels = mixedMoment B raw34525step0 raw34525step0Labels := by
      have hz : ∀ j, raw34525 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw34525step0 = (fun i j => raw34525 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw34525step0 raw34525; decide +kernel
      have hl : raw34525step0Labels = raw34525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34525 raw34525Labels permutation520 hz
    mixedMoment B raw34525step0 raw34525step0Labels = mixedMoment B raw34525step1 raw34525step1Labels := by
      have ha : raw34525step1 = (fun i j => raw34525step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34525step1 raw34525step0; decide +kernel
      have hl : raw34525step1Labels = raw34525step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34525step0 raw34525step0Labels permutation36 permutation3
    mixedMoment B raw34525step1 raw34525step1Labels = mixedMoment B raw34525step2 raw34525step2Labels := by
      have ha : raw34525step2 = raw34525step1 := by apply Matrix.ext; unfold raw34525step2 raw34525step1; decide +kernel
      have hl : raw34525step1Labels = labelEmbedding6 ∘ raw34525step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34525step1 raw34525step1Labels raw34525step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw34526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw34526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34526step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34526step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34526step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34526 raw34526Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw34526 raw34526Labels = mixedMoment B raw34526step0 raw34526step0Labels := by
      have ha : raw34526step0 = (fun i j => raw34526 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34526step0 raw34526; decide +kernel
      have hl : raw34526step0Labels = raw34526Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34526 raw34526Labels permutation171 permutation3
    mixedMoment B raw34526step0 raw34526step0Labels = mixedMoment B raw34526step1 raw34526step1Labels := by
      have ha : raw34526step1 = raw34526step0 := by apply Matrix.ext; unfold raw34526step1 raw34526step0; decide +kernel
      have hl : raw34526step0Labels = labelEmbedding6 ∘ raw34526step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34526step0 raw34526step0Labels raw34526step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

def raw34527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34527step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34527step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34527step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34527 raw34527Labels = mixedMoment B node4337 node4337Labels := by
  calc
    mixedMoment B raw34527 raw34527Labels = mixedMoment B raw34527step0 raw34527step0Labels := by
      have ha : raw34527step0 = (fun i j => raw34527 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34527step0 raw34527; decide +kernel
      have hl : raw34527step0Labels = raw34527Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34527 raw34527Labels permutation170 permutation3
    mixedMoment B raw34527step0 raw34527step0Labels = mixedMoment B raw34527step1 raw34527step1Labels := by
      have ha : raw34527step1 = raw34527step0 := by apply Matrix.ext; unfold raw34527step1 raw34527step0; decide +kernel
      have hl : raw34527step0Labels = labelEmbedding6 ∘ raw34527step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34527step0 raw34527step0Labels raw34527step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4337 node4337Labels := by rfl

def raw34528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34528step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34528step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34528step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34528 raw34528Labels = mixedMoment B node4936 node4936Labels := by
  calc
    mixedMoment B raw34528 raw34528Labels = mixedMoment B raw34528step0 raw34528step0Labels := by
      have ha : raw34528step0 = (fun i j => raw34528 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34528step0 raw34528; decide +kernel
      have hl : raw34528step0Labels = raw34528Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34528 raw34528Labels permutation170 permutation3
    mixedMoment B raw34528step0 raw34528step0Labels = mixedMoment B raw34528step1 raw34528step1Labels := by
      have ha : raw34528step1 = raw34528step0 := by apply Matrix.ext; unfold raw34528step1 raw34528step0; decide +kernel
      have hl : raw34528step0Labels = labelEmbedding6 ∘ raw34528step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34528step0 raw34528step0Labels raw34528step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4936 node4936Labels := by rfl

def raw34529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw34529step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34529step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34529step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34529step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34529 raw34529Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw34529 raw34529Labels = mixedMoment B raw34529step0 raw34529step0Labels := by
      have hz : ∀ j, raw34529 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34529step0 = (fun i j => raw34529 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34529step0 raw34529; decide +kernel
      have hl : raw34529step0Labels = raw34529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34529 raw34529Labels permutation434 hz
    mixedMoment B raw34529step0 raw34529step0Labels = mixedMoment B raw34529step1 raw34529step1Labels := by
      have ha : raw34529step1 = (fun i j => raw34529step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34529step1 raw34529step0; decide +kernel
      have hl : raw34529step1Labels = raw34529step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34529step0 raw34529step0Labels permutation36 permutation3
    mixedMoment B raw34529step1 raw34529step1Labels = mixedMoment B raw34529step2 raw34529step2Labels := by
      have ha : raw34529step2 = raw34529step1 := by apply Matrix.ext; unfold raw34529step2 raw34529step1; decide +kernel
      have hl : raw34529step1Labels = labelEmbedding6 ∘ raw34529step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34529step1 raw34529step1Labels raw34529step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw34530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw34530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34530step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw34530step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34530 raw34530Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw34530 raw34530Labels = mixedMoment B raw34530step0 raw34530step0Labels := by
      have ha : raw34530step0 = (fun i j => raw34530 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34530step0 raw34530; decide +kernel
      have hl : raw34530step0Labels = raw34530Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34530 raw34530Labels permutation170 permutation3
    mixedMoment B raw34530step0 raw34530step0Labels = mixedMoment B raw34530step1 raw34530step1Labels := by
      have ha : raw34530step1 = raw34530step0 := by apply Matrix.ext; unfold raw34530step1 raw34530step0; decide +kernel
      have hl : raw34530step0Labels = labelEmbedding6 ∘ raw34530step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34530step0 raw34530step0Labels raw34530step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

def raw34531 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw34531Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34531step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34531step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34531step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw34531step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34531 raw34531Labels = mixedMoment B node5166 node5166Labels := by
  calc
    mixedMoment B raw34531 raw34531Labels = mixedMoment B raw34531step0 raw34531step0Labels := by
      have ha : raw34531step0 = (fun i j => raw34531 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34531step0 raw34531; decide +kernel
      have hl : raw34531step0Labels = raw34531Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34531 raw34531Labels permutation152 permutation7
    mixedMoment B raw34531step0 raw34531step0Labels = mixedMoment B raw34531step1 raw34531step1Labels := by
      have ha : raw34531step1 = raw34531step0 := by apply Matrix.ext; unfold raw34531step1 raw34531step0; decide +kernel
      have hl : raw34531step0Labels = labelEmbedding10 ∘ raw34531step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34531step0 raw34531step0Labels raw34531step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5166 node5166Labels := by rfl

def raw34532 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw34532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34532step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34532step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34532step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34532 raw34532Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw34532 raw34532Labels = mixedMoment B raw34532step0 raw34532step0Labels := by
      have ha : raw34532step0 = (fun i j => raw34532 (permutation160 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34532step0 raw34532; decide +kernel
      have hl : raw34532step0Labels = raw34532Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34532 raw34532Labels permutation160 permutation7
    mixedMoment B raw34532step0 raw34532step0Labels = mixedMoment B raw34532step1 raw34532step1Labels := by
      have ha : raw34532step1 = raw34532step0 := by apply Matrix.ext; unfold raw34532step1 raw34532step0; decide +kernel
      have hl : raw34532step0Labels = labelEmbedding10 ∘ raw34532step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34532step0 raw34532step0Labels raw34532step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5098 node5098Labels := by rfl

def raw34533 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw34533Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34533step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34533step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34533step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34533 raw34533Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw34533 raw34533Labels = mixedMoment B raw34533step0 raw34533step0Labels := by
      have ha : raw34533step0 = (fun i j => raw34533 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34533step0 raw34533; decide +kernel
      have hl : raw34533step0Labels = raw34533Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34533 raw34533Labels permutation154 permutation7
    mixedMoment B raw34533step0 raw34533step0Labels = mixedMoment B raw34533step1 raw34533step1Labels := by
      have ha : raw34533step1 = raw34533step0 := by apply Matrix.ext; unfold raw34533step1 raw34533step0; decide +kernel
      have hl : raw34533step0Labels = labelEmbedding10 ∘ raw34533step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34533step0 raw34533step0Labels raw34533step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5098 node5098Labels := by rfl

def raw34534 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34534step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34534step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34534step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34534 raw34534Labels = mixedMoment B node5098 node5098Labels := by
  calc
    mixedMoment B raw34534 raw34534Labels = mixedMoment B raw34534step0 raw34534step0Labels := by
      have ha : raw34534step0 = (fun i j => raw34534 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34534step0 raw34534; decide +kernel
      have hl : raw34534step0Labels = raw34534Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34534 raw34534Labels permutation152 permutation7
    mixedMoment B raw34534step0 raw34534step0Labels = mixedMoment B raw34534step1 raw34534step1Labels := by
      have ha : raw34534step1 = raw34534step0 := by apply Matrix.ext; unfold raw34534step1 raw34534step0; decide +kernel
      have hl : raw34534step0Labels = labelEmbedding10 ∘ raw34534step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34534step0 raw34534step0Labels raw34534step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5098 node5098Labels := by rfl

def raw34535 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw34535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34535step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34535step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw34535step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34535 raw34535Labels = mixedMoment B node5097 node5097Labels := by
  calc
    mixedMoment B raw34535 raw34535Labels = mixedMoment B raw34535step0 raw34535step0Labels := by
      have ha : raw34535step0 = (fun i j => raw34535 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34535step0 raw34535; decide +kernel
      have hl : raw34535step0Labels = raw34535Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34535 raw34535Labels permutation152 permutation7
    mixedMoment B raw34535step0 raw34535step0Labels = mixedMoment B raw34535step1 raw34535step1Labels := by
      have ha : raw34535step1 = raw34535step0 := by apply Matrix.ext; unfold raw34535step1 raw34535step0; decide +kernel
      have hl : raw34535step0Labels = labelEmbedding10 ∘ raw34535step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34535step0 raw34535step0Labels raw34535step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5097 node5097Labels := by rfl

def raw34536 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw34536Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34536step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw34536step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34536step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34536step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34536step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34536step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34536 raw34536Labels = mixedMoment B node4859 node4859Labels := by
  calc
    mixedMoment B raw34536 raw34536Labels = mixedMoment B raw34536step0 raw34536step0Labels := by
      have ha : raw34536step0 = (fun i j => raw34536 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34536step0 raw34536; decide +kernel
      have hl : raw34536step0Labels = raw34536Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34536 raw34536Labels permutation246 permutation4
    mixedMoment B raw34536step0 raw34536step0Labels = mixedMoment B raw34536step1 raw34536step1Labels := by
      have ha : raw34536step1 = -raw34536step0 := by apply Matrix.ext; change ∀ i j, raw34536step1 i j = -(raw34536step0 i j); unfold raw34536step1 raw34536step0; decide +kernel
      have hl : raw34536step1Labels = raw34536step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34536step1 raw34536step1Labels = mixedMoment B raw34536step2 raw34536step2Labels := by
      have ha : raw34536step2 = raw34536step1 := by apply Matrix.ext; unfold raw34536step2 raw34536step1; decide +kernel
      have hl : raw34536step1Labels = labelEmbedding7 ∘ raw34536step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34536step1 raw34536step1Labels raw34536step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4859 node4859Labels := by rfl

def raw34537 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw34537Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34537step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34537step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34537step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34537 raw34537Labels = mixedMoment B node5197 node5197Labels := by
  calc
    mixedMoment B raw34537 raw34537Labels = mixedMoment B raw34537step0 raw34537step0Labels := by
      have ha : raw34537step0 = (fun i j => raw34537 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34537step0 raw34537; decide +kernel
      have hl : raw34537step0Labels = raw34537Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34537 raw34537Labels permutation170 permutation6
    mixedMoment B raw34537step0 raw34537step0Labels = mixedMoment B raw34537step1 raw34537step1Labels := by
      have ha : raw34537step1 = raw34537step0 := by apply Matrix.ext; unfold raw34537step1 raw34537step0; decide +kernel
      have hl : raw34537step0Labels = labelEmbedding9 ∘ raw34537step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34537step0 raw34537step0Labels raw34537step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5197 node5197Labels := by rfl

def raw34538 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw34538Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34538step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34538step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34538step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34538 raw34538Labels = mixedMoment B node5197 node5197Labels := by
  calc
    mixedMoment B raw34538 raw34538Labels = mixedMoment B raw34538step0 raw34538step0Labels := by
      have ha : raw34538step0 = (fun i j => raw34538 (permutation172 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34538step0 raw34538; decide +kernel
      have hl : raw34538step0Labels = raw34538Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34538 raw34538Labels permutation172 permutation6
    mixedMoment B raw34538step0 raw34538step0Labels = mixedMoment B raw34538step1 raw34538step1Labels := by
      have ha : raw34538step1 = raw34538step0 := by apply Matrix.ext; unfold raw34538step1 raw34538step0; decide +kernel
      have hl : raw34538step0Labels = labelEmbedding9 ∘ raw34538step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34538step0 raw34538step0Labels raw34538step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5197 node5197Labels := by rfl

def raw34539 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34539step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34539step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34539step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34539 raw34539Labels = mixedMoment B node5197 node5197Labels := by
  calc
    mixedMoment B raw34539 raw34539Labels = mixedMoment B raw34539step0 raw34539step0Labels := by
      have ha : raw34539step0 = (fun i j => raw34539 (permutation174 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34539step0 raw34539; decide +kernel
      have hl : raw34539step0Labels = raw34539Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34539 raw34539Labels permutation174 permutation6
    mixedMoment B raw34539step0 raw34539step0Labels = mixedMoment B raw34539step1 raw34539step1Labels := by
      have ha : raw34539step1 = raw34539step0 := by apply Matrix.ext; unfold raw34539step1 raw34539step0; decide +kernel
      have hl : raw34539step0Labels = labelEmbedding9 ∘ raw34539step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34539step0 raw34539step0Labels raw34539step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5197 node5197Labels := by rfl

def raw34540 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw34540Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34540step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34540step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34540step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34540 raw34540Labels = mixedMoment B node5194 node5194Labels := by
  calc
    mixedMoment B raw34540 raw34540Labels = mixedMoment B raw34540step0 raw34540step0Labels := by
      have ha : raw34540step0 = (fun i j => raw34540 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34540step0 raw34540; decide +kernel
      have hl : raw34540step0Labels = raw34540Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34540 raw34540Labels permutation170 permutation6
    mixedMoment B raw34540step0 raw34540step0Labels = mixedMoment B raw34540step1 raw34540step1Labels := by
      have ha : raw34540step1 = raw34540step0 := by apply Matrix.ext; unfold raw34540step1 raw34540step0; decide +kernel
      have hl : raw34540step0Labels = labelEmbedding9 ∘ raw34540step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34540step0 raw34540step0Labels raw34540step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5194 node5194Labels := by rfl

def raw34541 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw34541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34541step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34541step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34541step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34541 raw34541Labels = mixedMoment B node4826 node4826Labels := by
  calc
    mixedMoment B raw34541 raw34541Labels = mixedMoment B raw34541step0 raw34541step0Labels := by
      have ha : raw34541step0 = (fun i j => raw34541 (permutation173 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34541step0 raw34541; decide +kernel
      have hl : raw34541step0Labels = raw34541Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34541 raw34541Labels permutation173 permutation6
    mixedMoment B raw34541step0 raw34541step0Labels = mixedMoment B raw34541step1 raw34541step1Labels := by
      have ha : raw34541step1 = raw34541step0 := by apply Matrix.ext; unfold raw34541step1 raw34541step0; decide +kernel
      have hl : raw34541step0Labels = labelEmbedding9 ∘ raw34541step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34541step0 raw34541step0Labels raw34541step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4826 node4826Labels := by rfl

def raw34542 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw34542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34542step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34542step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34542step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34542 raw34542Labels = mixedMoment B node5093 node5093Labels := by
  calc
    mixedMoment B raw34542 raw34542Labels = mixedMoment B raw34542step0 raw34542step0Labels := by
      have ha : raw34542step0 = (fun i j => raw34542 (permutation173 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34542step0 raw34542; decide +kernel
      have hl : raw34542step0Labels = raw34542Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34542 raw34542Labels permutation173 permutation6
    mixedMoment B raw34542step0 raw34542step0Labels = mixedMoment B raw34542step1 raw34542step1Labels := by
      have ha : raw34542step1 = raw34542step0 := by apply Matrix.ext; unfold raw34542step1 raw34542step0; decide +kernel
      have hl : raw34542step0Labels = labelEmbedding9 ∘ raw34542step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34542step0 raw34542step0Labels raw34542step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5093 node5093Labels := by rfl

def raw34543 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw34543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34543step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34543step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34543step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34543 raw34543Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw34543 raw34543Labels = mixedMoment B raw34543step0 raw34543step0Labels := by
      have ha : raw34543step0 = (fun i j => raw34543 (permutation173 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34543step0 raw34543; decide +kernel
      have hl : raw34543step0Labels = raw34543Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34543 raw34543Labels permutation173 permutation6
    mixedMoment B raw34543step0 raw34543step0Labels = mixedMoment B raw34543step1 raw34543step1Labels := by
      have ha : raw34543step1 = raw34543step0 := by apply Matrix.ext; unfold raw34543step1 raw34543step0; decide +kernel
      have hl : raw34543step0Labels = labelEmbedding9 ∘ raw34543step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34543step0 raw34543step0Labels raw34543step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw34544 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34544step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34544 raw34544Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw34544 raw34544Labels = mixedMoment B raw34544step0 raw34544step0Labels := by
      have ha : raw34544step0 = (fun i j => raw34544 (permutation175 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34544step0 raw34544; decide +kernel
      have hl : raw34544step0Labels = raw34544Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34544 raw34544Labels permutation175 permutation6
    mixedMoment B raw34544step0 raw34544step0Labels = mixedMoment B raw34544step1 raw34544step1Labels := by
      have ha : raw34544step1 = raw34544step0 := by apply Matrix.ext; unfold raw34544step1 raw34544step0; decide +kernel
      have hl : raw34544step0Labels = labelEmbedding9 ∘ raw34544step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34544step0 raw34544step0Labels raw34544step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw34545 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw34545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34545step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34545step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34545 raw34545Labels = mixedMoment B node5157 node5157Labels := by
  calc
    mixedMoment B raw34545 raw34545Labels = mixedMoment B raw34545step0 raw34545step0Labels := by
      have ha : raw34545step0 = (fun i j => raw34545 (permutation173 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34545step0 raw34545; decide +kernel
      have hl : raw34545step0Labels = raw34545Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34545 raw34545Labels permutation173 permutation6
    mixedMoment B raw34545step0 raw34545step0Labels = mixedMoment B raw34545step1 raw34545step1Labels := by
      have ha : raw34545step1 = raw34545step0 := by apply Matrix.ext; unfold raw34545step1 raw34545step0; decide +kernel
      have hl : raw34545step0Labels = labelEmbedding9 ∘ raw34545step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34545step0 raw34545step0Labels raw34545step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5157 node5157Labels := by rfl

def raw34546 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw34546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34546step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34546step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34546step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34546 raw34546Labels = mixedMoment B node4826 node4826Labels := by
  calc
    mixedMoment B raw34546 raw34546Labels = mixedMoment B raw34546step0 raw34546step0Labels := by
      have ha : raw34546step0 = (fun i j => raw34546 (permutation171 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34546step0 raw34546; decide +kernel
      have hl : raw34546step0Labels = raw34546Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34546 raw34546Labels permutation171 permutation6
    mixedMoment B raw34546step0 raw34546step0Labels = mixedMoment B raw34546step1 raw34546step1Labels := by
      have ha : raw34546step1 = raw34546step0 := by apply Matrix.ext; unfold raw34546step1 raw34546step0; decide +kernel
      have hl : raw34546step0Labels = labelEmbedding9 ∘ raw34546step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34546step0 raw34546step0Labels raw34546step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4826 node4826Labels := by rfl

def raw34547 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw34547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34547step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34547step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34547 raw34547Labels = mixedMoment B node5093 node5093Labels := by
  calc
    mixedMoment B raw34547 raw34547Labels = mixedMoment B raw34547step0 raw34547step0Labels := by
      have ha : raw34547step0 = (fun i j => raw34547 (permutation171 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34547step0 raw34547; decide +kernel
      have hl : raw34547step0Labels = raw34547Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34547 raw34547Labels permutation171 permutation6
    mixedMoment B raw34547step0 raw34547step0Labels = mixedMoment B raw34547step1 raw34547step1Labels := by
      have ha : raw34547step1 = raw34547step0 := by apply Matrix.ext; unfold raw34547step1 raw34547step0; decide +kernel
      have hl : raw34547step0Labels = labelEmbedding9 ∘ raw34547step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34547step0 raw34547step0Labels raw34547step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5093 node5093Labels := by rfl

def raw34548 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw34548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34548step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34548step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34548 raw34548Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw34548 raw34548Labels = mixedMoment B raw34548step0 raw34548step0Labels := by
      have ha : raw34548step0 = (fun i j => raw34548 (permutation171 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34548step0 raw34548; decide +kernel
      have hl : raw34548step0Labels = raw34548Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34548 raw34548Labels permutation171 permutation6
    mixedMoment B raw34548step0 raw34548step0Labels = mixedMoment B raw34548step1 raw34548step1Labels := by
      have ha : raw34548step1 = raw34548step0 := by apply Matrix.ext; unfold raw34548step1 raw34548step0; decide +kernel
      have hl : raw34548step0Labels = labelEmbedding9 ∘ raw34548step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34548step0 raw34548step0Labels raw34548step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw34549 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw34549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34549step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34549step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34549 raw34549Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw34549 raw34549Labels = mixedMoment B raw34549step0 raw34549step0Labels := by
      have ha : raw34549step0 = (fun i j => raw34549 (permutation174 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34549step0 raw34549; decide +kernel
      have hl : raw34549step0Labels = raw34549Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34549 raw34549Labels permutation174 permutation6
    mixedMoment B raw34549step0 raw34549step0Labels = mixedMoment B raw34549step1 raw34549step1Labels := by
      have ha : raw34549step1 = raw34549step0 := by apply Matrix.ext; unfold raw34549step1 raw34549step0; decide +kernel
      have hl : raw34549step0Labels = labelEmbedding9 ∘ raw34549step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34549step0 raw34549step0Labels raw34549step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw34550 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw34550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34550step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34550step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34550 raw34550Labels = mixedMoment B node5157 node5157Labels := by
  calc
    mixedMoment B raw34550 raw34550Labels = mixedMoment B raw34550step0 raw34550step0Labels := by
      have ha : raw34550step0 = (fun i j => raw34550 (permutation171 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34550step0 raw34550; decide +kernel
      have hl : raw34550step0Labels = raw34550Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34550 raw34550Labels permutation171 permutation6
    mixedMoment B raw34550step0 raw34550step0Labels = mixedMoment B raw34550step1 raw34550step1Labels := by
      have ha : raw34550step1 = raw34550step0 := by apply Matrix.ext; unfold raw34550step1 raw34550step0; decide +kernel
      have hl : raw34550step0Labels = labelEmbedding9 ∘ raw34550step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34550step0 raw34550step0Labels raw34550step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5157 node5157Labels := by rfl

def raw34551 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw34551Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34551step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34551step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34551step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34551 raw34551Labels = mixedMoment B node4826 node4826Labels := by
  calc
    mixedMoment B raw34551 raw34551Labels = mixedMoment B raw34551step0 raw34551step0Labels := by
      have ha : raw34551step0 = (fun i j => raw34551 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34551step0 raw34551; decide +kernel
      have hl : raw34551step0Labels = raw34551Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34551 raw34551Labels permutation170 permutation6
    mixedMoment B raw34551step0 raw34551step0Labels = mixedMoment B raw34551step1 raw34551step1Labels := by
      have ha : raw34551step1 = raw34551step0 := by apply Matrix.ext; unfold raw34551step1 raw34551step0; decide +kernel
      have hl : raw34551step0Labels = labelEmbedding9 ∘ raw34551step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34551step0 raw34551step0Labels raw34551step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4826 node4826Labels := by rfl

def raw34552 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw34552Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34552step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34552step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34552step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34552 raw34552Labels = mixedMoment B node5093 node5093Labels := by
  calc
    mixedMoment B raw34552 raw34552Labels = mixedMoment B raw34552step0 raw34552step0Labels := by
      have ha : raw34552step0 = (fun i j => raw34552 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34552step0 raw34552; decide +kernel
      have hl : raw34552step0Labels = raw34552Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34552 raw34552Labels permutation170 permutation6
    mixedMoment B raw34552step0 raw34552step0Labels = mixedMoment B raw34552step1 raw34552step1Labels := by
      have ha : raw34552step1 = raw34552step0 := by apply Matrix.ext; unfold raw34552step1 raw34552step0; decide +kernel
      have hl : raw34552step0Labels = labelEmbedding9 ∘ raw34552step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34552step0 raw34552step0Labels raw34552step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5093 node5093Labels := by rfl

def raw34553 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw34553Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34553step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34553step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34553step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34553step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34553 raw34553Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw34553 raw34553Labels = mixedMoment B raw34553step0 raw34553step0Labels := by
      have ha : raw34553step0 = (fun i j => raw34553 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34553step0 raw34553; decide +kernel
      have hl : raw34553step0Labels = raw34553Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34553 raw34553Labels permutation170 permutation6
    mixedMoment B raw34553step0 raw34553step0Labels = mixedMoment B raw34553step1 raw34553step1Labels := by
      have ha : raw34553step1 = raw34553step0 := by apply Matrix.ext; unfold raw34553step1 raw34553step0; decide +kernel
      have hl : raw34553step0Labels = labelEmbedding9 ∘ raw34553step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34553step0 raw34553step0Labels raw34553step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw34554 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1], ![-2, 1, 1]]
def raw34554Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34554step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34554step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw34554step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34554 raw34554Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw34554 raw34554Labels = mixedMoment B raw34554step0 raw34554step0Labels := by
      have ha : raw34554step0 = (fun i j => raw34554 (permutation172 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34554step0 raw34554; decide +kernel
      have hl : raw34554step0Labels = raw34554Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34554 raw34554Labels permutation172 permutation6
    mixedMoment B raw34554step0 raw34554step0Labels = mixedMoment B raw34554step1 raw34554step1Labels := by
      have ha : raw34554step1 = raw34554step0 := by apply Matrix.ext; unfold raw34554step1 raw34554step0; decide +kernel
      have hl : raw34554step0Labels = labelEmbedding9 ∘ raw34554step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34554step0 raw34554step0Labels raw34554step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw34555 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![-3, 2, 1]]
def raw34555Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34555step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34555step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw34555step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34555 raw34555Labels = mixedMoment B node5157 node5157Labels := by
  calc
    mixedMoment B raw34555 raw34555Labels = mixedMoment B raw34555step0 raw34555step0Labels := by
      have ha : raw34555step0 = (fun i j => raw34555 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34555step0 raw34555; decide +kernel
      have hl : raw34555step0Labels = raw34555Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34555 raw34555Labels permutation170 permutation6
    mixedMoment B raw34555step0 raw34555step0Labels = mixedMoment B raw34555step1 raw34555step1Labels := by
      have ha : raw34555step1 = raw34555step0 := by apply Matrix.ext; unfold raw34555step1 raw34555step0; decide +kernel
      have hl : raw34555step0Labels = labelEmbedding9 ∘ raw34555step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34555step0 raw34555step0Labels raw34555step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5157 node5157Labels := by rfl

def raw34556 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw34556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34556step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34556step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34556 raw34556Labels = mixedMoment B node4833 node4833Labels := by
  calc
    mixedMoment B raw34556 raw34556Labels = mixedMoment B raw34556step0 raw34556step0Labels := by
      have ha : raw34556step0 = (fun i j => raw34556 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34556step0 raw34556; decide +kernel
      have hl : raw34556step0Labels = raw34556Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34556 raw34556Labels permutation170 permutation6
    mixedMoment B raw34556step0 raw34556step0Labels = mixedMoment B raw34556step1 raw34556step1Labels := by
      have ha : raw34556step1 = raw34556step0 := by apply Matrix.ext; unfold raw34556step1 raw34556step0; decide +kernel
      have hl : raw34556step0Labels = labelEmbedding9 ∘ raw34556step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34556step0 raw34556step0Labels raw34556step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4833 node4833Labels := by rfl

def raw34557 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw34557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34557step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34557step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw34557step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34557 raw34557Labels = mixedMoment B node5100 node5100Labels := by
  calc
    mixedMoment B raw34557 raw34557Labels = mixedMoment B raw34557step0 raw34557step0Labels := by
      have ha : raw34557step0 = (fun i j => raw34557 (permutation170 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34557step0 raw34557; decide +kernel
      have hl : raw34557step0Labels = raw34557Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34557 raw34557Labels permutation170 permutation6
    mixedMoment B raw34557step0 raw34557step0Labels = mixedMoment B raw34557step1 raw34557step1Labels := by
      have ha : raw34557step1 = raw34557step0 := by apply Matrix.ext; unfold raw34557step1 raw34557step0; decide +kernel
      have hl : raw34557step0Labels = labelEmbedding9 ∘ raw34557step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34557step0 raw34557step0Labels raw34557step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5100 node5100Labels := by rfl

def raw34558 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw34558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34558step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34558step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34558step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34558 raw34558Labels = mixedMoment B node5167 node5167Labels := by
  calc
    mixedMoment B raw34558 raw34558Labels = mixedMoment B raw34558step0 raw34558step0Labels := by
      have ha : raw34558step0 = (fun i j => raw34558 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34558step0 raw34558; decide +kernel
      have hl : raw34558step0Labels = raw34558Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34558 raw34558Labels permutation156 permutation6
    mixedMoment B raw34558step0 raw34558step0Labels = mixedMoment B raw34558step1 raw34558step1Labels := by
      have ha : raw34558step1 = raw34558step0 := by apply Matrix.ext; unfold raw34558step1 raw34558step0; decide +kernel
      have hl : raw34558step0Labels = labelEmbedding9 ∘ raw34558step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34558step0 raw34558step0Labels raw34558step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5167 node5167Labels := by rfl

def raw34559 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw34559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34559step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34559step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34559step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw34559step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34559 raw34559Labels = mixedMoment B node5167 node5167Labels := by
  calc
    mixedMoment B raw34559 raw34559Labels = mixedMoment B raw34559step0 raw34559step0Labels := by
      have ha : raw34559step0 = (fun i j => raw34559 (permutation162 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34559step0 raw34559; decide +kernel
      have hl : raw34559step0Labels = raw34559Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34559 raw34559Labels permutation162 permutation6
    mixedMoment B raw34559step0 raw34559step0Labels = mixedMoment B raw34559step1 raw34559step1Labels := by
      have ha : raw34559step1 = raw34559step0 := by apply Matrix.ext; unfold raw34559step1 raw34559step0; decide +kernel
      have hl : raw34559step0Labels = labelEmbedding9 ∘ raw34559step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34559step0 raw34559step0Labels raw34559step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5167 node5167Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
