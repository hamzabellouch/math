import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw16256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16256step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16256step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16256 raw16256Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw16256 raw16256Labels = mixedMoment B raw16256step0 raw16256step0Labels := by
      have hz : ∀ j, raw16256 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16256step0 = (fun i j => raw16256 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16256step0 raw16256; decide +kernel
      have hl : raw16256step0Labels = raw16256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16256 raw16256Labels permutation346 hz
    mixedMoment B raw16256step0 raw16256step0Labels = mixedMoment B raw16256step1 raw16256step1Labels := by
      have ha : raw16256step1 = (fun i j => raw16256step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16256step1 raw16256step0; decide +kernel
      have hl : raw16256step1Labels = raw16256step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16256step0 raw16256step0Labels permutation149 permutation3
    mixedMoment B raw16256step1 raw16256step1Labels = mixedMoment B raw16256step2 raw16256step2Labels := by
      have ha : raw16256step2 = -raw16256step1 := by apply Matrix.ext; change ∀ i j, raw16256step2 i j = -(raw16256step1 i j); unfold raw16256step2 raw16256step1; decide +kernel
      have hl : raw16256step2Labels = raw16256step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw16257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16257Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16257step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16257step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw16257step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16257step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw16257step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16257step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-2, 2, 0]]
def raw16257step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16257step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![2, -2, 0]]
def raw16257step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16257 raw16257Labels = mixedMoment B node4019 node4019Labels := by
  calc
    mixedMoment B raw16257 raw16257Labels = mixedMoment B raw16257step0 raw16257step0Labels := by
      have hz : ∀ j, raw16257 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16257step0 = (fun i j => raw16257 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16257step0 raw16257; decide +kernel
      have hl : raw16257step0Labels = raw16257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16257 raw16257Labels permutation520 hz
    mixedMoment B raw16257step0 raw16257step0Labels = mixedMoment B raw16257step1 raw16257step1Labels := by
      have hz : ∀ j, raw16257step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw16257step1 = (fun i j => raw16257step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw16257step1 raw16257step0; decide +kernel
      have hl : raw16257step1Labels = raw16257step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16257step0 raw16257step0Labels permutation104 hz
    mixedMoment B raw16257step1 raw16257step1Labels = mixedMoment B raw16257step2 raw16257step2Labels := by
      have hz : ∀ j, raw16257step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw16257step2 = (fun i j => raw16257step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw16257step2 raw16257step1; decide +kernel
      have hl : raw16257step2Labels = raw16257step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16257step1 raw16257step1Labels permutation20 hz
    mixedMoment B raw16257step2 raw16257step2Labels = mixedMoment B raw16257step3 raw16257step3Labels := by
      have ha : raw16257step3 = (fun i j => raw16257step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16257step3 raw16257step2; decide +kernel
      have hl : raw16257step3Labels = raw16257step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16257step2 raw16257step2Labels permutation7 permutation3
    mixedMoment B raw16257step3 raw16257step3Labels = mixedMoment B raw16257step4 raw16257step4Labels := by
      have ha : raw16257step4 = -raw16257step3 := by apply Matrix.ext; change ∀ i j, raw16257step4 i j = -(raw16257step3 i j); unfold raw16257step4 raw16257step3; decide +kernel
      have hl : raw16257step4Labels = raw16257step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4019 node4019Labels := by rfl

def raw16258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16258Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16258step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16258step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw16258step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16258step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16258 raw16258Labels = mixedMoment B node4040 node4040Labels := by
  calc
    mixedMoment B raw16258 raw16258Labels = mixedMoment B raw16258step0 raw16258step0Labels := by
      have hz : ∀ j, raw16258 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16258step0 = (fun i j => raw16258 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16258step0 raw16258; decide +kernel
      have hl : raw16258step0Labels = raw16258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16258 raw16258Labels permutation434 hz
    mixedMoment B raw16258step0 raw16258step0Labels = mixedMoment B raw16258step1 raw16258step1Labels := by
      have hz : ∀ j, raw16258step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16258step1 = (fun i j => raw16258step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16258step1 raw16258step0; decide +kernel
      have hl : raw16258step1Labels = raw16258step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16258step0 raw16258step0Labels permutation80 hz
    mixedMoment B raw16258step1 raw16258step1Labels = mixedMoment B raw16258step2 raw16258step2Labels := by
      have ha : raw16258step2 = (fun i j => raw16258step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16258step2 raw16258step1; decide +kernel
      have hl : raw16258step2Labels = raw16258step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16258step1 raw16258step1Labels permutation9 permutation3
    _ = mixedMoment B node4040 node4040Labels := by rfl

def raw16259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16259Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16259step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16259step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16259step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16259 raw16259Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw16259 raw16259Labels = mixedMoment B raw16259step0 raw16259step0Labels := by
      have hz : ∀ j, raw16259 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16259step0 = (fun i j => raw16259 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16259step0 raw16259; decide +kernel
      have hl : raw16259step0Labels = raw16259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16259 raw16259Labels permutation434 hz
    mixedMoment B raw16259step0 raw16259step0Labels = mixedMoment B raw16259step1 raw16259step1Labels := by
      have ha : raw16259step1 = (fun i j => raw16259step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16259step1 raw16259step0; decide +kernel
      have hl : raw16259step1Labels = raw16259step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16259step0 raw16259step0Labels permutation32 permutation3
    _ = mixedMoment B node2884 node2884Labels := by rfl

def raw16260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16260Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16260step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16260step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16260 raw16260Labels = mixedMoment B node3394 node3394Labels := by
  calc
    mixedMoment B raw16260 raw16260Labels = mixedMoment B raw16260step0 raw16260step0Labels := by
      have hz : ∀ j, raw16260 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16260step0 = (fun i j => raw16260 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16260step0 raw16260; decide +kernel
      have hl : raw16260step0Labels = raw16260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16260 raw16260Labels permutation434 hz
    mixedMoment B raw16260step0 raw16260step0Labels = mixedMoment B raw16260step1 raw16260step1Labels := by
      have ha : raw16260step1 = (fun i j => raw16260step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16260step1 raw16260step0; decide +kernel
      have hl : raw16260step1Labels = raw16260step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16260step0 raw16260step0Labels permutation56 permutation3
    _ = mixedMoment B node3394 node3394Labels := by rfl

def raw16261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16261Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16261step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16261step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16261step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16261 raw16261Labels = mixedMoment B node3964 node3964Labels := by
  calc
    mixedMoment B raw16261 raw16261Labels = mixedMoment B raw16261step0 raw16261step0Labels := by
      have ha : raw16261step0 = (fun i j => raw16261 (permutation646 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16261step0 raw16261; decide +kernel
      have hl : raw16261step0Labels = raw16261Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16261 raw16261Labels permutation646 permutation3
    mixedMoment B raw16261step0 raw16261step0Labels = mixedMoment B raw16261step1 raw16261step1Labels := by
      have ha : raw16261step1 = -raw16261step0 := by apply Matrix.ext; change ∀ i j, raw16261step1 i j = -(raw16261step0 i j); unfold raw16261step1 raw16261step0; decide +kernel
      have hl : raw16261step1Labels = raw16261step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3964 node3964Labels := by rfl

def raw16262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16262Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16262step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16262step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16262step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16262step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16262step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16262step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16262step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16262 raw16262Labels = mixedMoment B node3987 node3987Labels := by
  calc
    mixedMoment B raw16262 raw16262Labels = mixedMoment B raw16262step0 raw16262step0Labels := by
      have hz : ∀ j, raw16262 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16262step0 = (fun i j => raw16262 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16262step0 raw16262; decide +kernel
      have hl : raw16262step0Labels = raw16262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16262 raw16262Labels permutation520 hz
    mixedMoment B raw16262step0 raw16262step0Labels = mixedMoment B raw16262step1 raw16262step1Labels := by
      have hz : ∀ j, raw16262step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw16262step1 = (fun i j => raw16262step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw16262step1 raw16262step0; decide +kernel
      have hl : raw16262step1Labels = raw16262step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16262step0 raw16262step0Labels permutation104 hz
    mixedMoment B raw16262step1 raw16262step1Labels = mixedMoment B raw16262step2 raw16262step2Labels := by
      have ha : raw16262step2 = (fun i j => raw16262step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16262step2 raw16262step1; decide +kernel
      have hl : raw16262step2Labels = raw16262step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16262step1 raw16262step1Labels permutation31 permutation3
    mixedMoment B raw16262step2 raw16262step2Labels = mixedMoment B raw16262step3 raw16262step3Labels := by
      have ha : raw16262step3 = -raw16262step2 := by apply Matrix.ext; change ∀ i j, raw16262step3 i j = -(raw16262step2 i j); unfold raw16262step3 raw16262step2; decide +kernel
      have hl : raw16262step3Labels = raw16262step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3987 node3987Labels := by rfl

def raw16263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16263Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16263step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16263step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16263 raw16263Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw16263 raw16263Labels = mixedMoment B raw16263step0 raw16263step0Labels := by
      have hz : ∀ j, raw16263 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16263step0 = (fun i j => raw16263 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16263step0 raw16263; decide +kernel
      have hl : raw16263step0Labels = raw16263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16263 raw16263Labels permutation434 hz
    mixedMoment B raw16263step0 raw16263step0Labels = mixedMoment B raw16263step1 raw16263step1Labels := by
      have ha : raw16263step1 = (fun i j => raw16263step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16263step1 raw16263step0; decide +kernel
      have hl : raw16263step1Labels = raw16263step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16263step0 raw16263step0Labels permutation36 permutation3
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw16264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16264Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16264step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16264step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16264step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16264 raw16264Labels = mixedMoment B node2884 node2884Labels := by
  calc
    mixedMoment B raw16264 raw16264Labels = mixedMoment B raw16264step0 raw16264step0Labels := by
      have hz : ∀ j, raw16264 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16264step0 = (fun i j => raw16264 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16264step0 raw16264; decide +kernel
      have hl : raw16264step0Labels = raw16264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16264 raw16264Labels permutation346 hz
    mixedMoment B raw16264step0 raw16264step0Labels = mixedMoment B raw16264step1 raw16264step1Labels := by
      have ha : raw16264step1 = (fun i j => raw16264step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16264step1 raw16264step0; decide +kernel
      have hl : raw16264step1Labels = raw16264step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16264step0 raw16264step0Labels permutation32 permutation3
    _ = mixedMoment B node2884 node2884Labels := by rfl

def raw16265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16265Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16265step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16265step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16265 raw16265Labels = mixedMoment B node3394 node3394Labels := by
  calc
    mixedMoment B raw16265 raw16265Labels = mixedMoment B raw16265step0 raw16265step0Labels := by
      have hz : ∀ j, raw16265 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16265step0 = (fun i j => raw16265 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16265step0 raw16265; decide +kernel
      have hl : raw16265step0Labels = raw16265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16265 raw16265Labels permutation346 hz
    mixedMoment B raw16265step0 raw16265step0Labels = mixedMoment B raw16265step1 raw16265step1Labels := by
      have ha : raw16265step1 = (fun i j => raw16265step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16265step1 raw16265step0; decide +kernel
      have hl : raw16265step1Labels = raw16265step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16265step0 raw16265step0Labels permutation56 permutation3
    _ = mixedMoment B node3394 node3394Labels := by rfl

def raw16266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16266Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16266step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16266step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16266step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16266 raw16266Labels = mixedMoment B node3964 node3964Labels := by
  calc
    mixedMoment B raw16266 raw16266Labels = mixedMoment B raw16266step0 raw16266step0Labels := by
      have ha : raw16266step0 = (fun i j => raw16266 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16266step0 raw16266; decide +kernel
      have hl : raw16266step0Labels = raw16266Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16266 raw16266Labels permutation664 permutation3
    mixedMoment B raw16266step0 raw16266step0Labels = mixedMoment B raw16266step1 raw16266step1Labels := by
      have ha : raw16266step1 = -raw16266step0 := by apply Matrix.ext; change ∀ i j, raw16266step1 i j = -(raw16266step0 i j); unfold raw16266step1 raw16266step0; decide +kernel
      have hl : raw16266step1Labels = raw16266step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3964 node3964Labels := by rfl

def raw16267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw16267Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw16267step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16267step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16267step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16267step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16267step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16267step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw16267step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16267 raw16267Labels = mixedMoment B node3987 node3987Labels := by
  calc
    mixedMoment B raw16267 raw16267Labels = mixedMoment B raw16267step0 raw16267step0Labels := by
      have hz : ∀ j, raw16267 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16267step0 = (fun i j => raw16267 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16267step0 raw16267; decide +kernel
      have hl : raw16267step0Labels = raw16267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16267 raw16267Labels permutation520 hz
    mixedMoment B raw16267step0 raw16267step0Labels = mixedMoment B raw16267step1 raw16267step1Labels := by
      have hz : ∀ j, raw16267step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16267step1 = (fun i j => raw16267step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16267step1 raw16267step0; decide +kernel
      have hl : raw16267step1Labels = raw16267step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16267step0 raw16267step0Labels permutation80 hz
    mixedMoment B raw16267step1 raw16267step1Labels = mixedMoment B raw16267step2 raw16267step2Labels := by
      have ha : raw16267step2 = (fun i j => raw16267step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16267step2 raw16267step1; decide +kernel
      have hl : raw16267step2Labels = raw16267step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16267step1 raw16267step1Labels permutation31 permutation3
    mixedMoment B raw16267step2 raw16267step2Labels = mixedMoment B raw16267step3 raw16267step3Labels := by
      have ha : raw16267step3 = -raw16267step2 := by apply Matrix.ext; change ∀ i j, raw16267step3 i j = -(raw16267step2 i j); unfold raw16267step3 raw16267step2; decide +kernel
      have hl : raw16267step3Labels = raw16267step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3987 node3987Labels := by rfl

def raw16268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16268Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16268step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16268step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16268 raw16268Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw16268 raw16268Labels = mixedMoment B raw16268step0 raw16268step0Labels := by
      have hz : ∀ j, raw16268 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16268step0 = (fun i j => raw16268 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16268step0 raw16268; decide +kernel
      have hl : raw16268step0Labels = raw16268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16268 raw16268Labels permutation346 hz
    mixedMoment B raw16268step0 raw16268step0Labels = mixedMoment B raw16268step1 raw16268step1Labels := by
      have ha : raw16268step1 = (fun i j => raw16268step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16268step1 raw16268step0; decide +kernel
      have hl : raw16268step1Labels = raw16268step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16268step0 raw16268step0Labels permutation36 permutation3
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw16269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16269Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16269step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16269step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16269step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16269step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw16269step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16269 raw16269Labels = mixedMoment B node2889 node2889Labels := by
  calc
    mixedMoment B raw16269 raw16269Labels = mixedMoment B raw16269step0 raw16269step0Labels := by
      have hz : ∀ j, raw16269 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16269step0 = (fun i j => raw16269 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16269step0 raw16269; decide +kernel
      have hl : raw16269step0Labels = raw16269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16269 raw16269Labels permutation434 hz
    mixedMoment B raw16269step0 raw16269step0Labels = mixedMoment B raw16269step1 raw16269step1Labels := by
      have hz : ∀ j, raw16269step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16269step1 = (fun i j => raw16269step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16269step1 raw16269step0; decide +kernel
      have hl : raw16269step1Labels = raw16269step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16269step0 raw16269step0Labels permutation80 hz
    mixedMoment B raw16269step1 raw16269step1Labels = mixedMoment B raw16269step2 raw16269step2Labels := by
      have ha : raw16269step2 = (fun i j => raw16269step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16269step2 raw16269step1; decide +kernel
      have hl : raw16269step2Labels = raw16269step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16269step1 raw16269step1Labels permutation9 permutation3
    _ = mixedMoment B node2889 node2889Labels := by rfl

def raw16270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16270Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16270step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16270step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![2, -2, 0], ![2, -1, -1]]
def raw16270step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16270step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![2, -1, -1], ![2, 0, -2]]
def raw16270step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16270 raw16270Labels = mixedMoment B node3397 node3397Labels := by
  calc
    mixedMoment B raw16270 raw16270Labels = mixedMoment B raw16270step0 raw16270step0Labels := by
      have hz : ∀ j, raw16270 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16270step0 = (fun i j => raw16270 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16270step0 raw16270; decide +kernel
      have hl : raw16270step0Labels = raw16270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16270 raw16270Labels permutation434 hz
    mixedMoment B raw16270step0 raw16270step0Labels = mixedMoment B raw16270step1 raw16270step1Labels := by
      have hz : ∀ j, raw16270step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16270step1 = (fun i j => raw16270step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16270step1 raw16270step0; decide +kernel
      have hl : raw16270step1Labels = raw16270step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16270step0 raw16270step0Labels permutation80 hz
    mixedMoment B raw16270step1 raw16270step1Labels = mixedMoment B raw16270step2 raw16270step2Labels := by
      have ha : raw16270step2 = (fun i j => raw16270step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16270step2 raw16270step1; decide +kernel
      have hl : raw16270step2Labels = raw16270step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16270step1 raw16270step1Labels permutation15 permutation3
    _ = mixedMoment B node3397 node3397Labels := by rfl

def raw16271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16271Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16271step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16271step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16271step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16271step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16271 raw16271Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw16271 raw16271Labels = mixedMoment B raw16271step0 raw16271step0Labels := by
      have hz : ∀ j, raw16271 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16271step0 = (fun i j => raw16271 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16271step0 raw16271; decide +kernel
      have hl : raw16271step0Labels = raw16271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16271 raw16271Labels permutation434 hz
    mixedMoment B raw16271step0 raw16271step0Labels = mixedMoment B raw16271step1 raw16271step1Labels := by
      have ha : raw16271step1 = (fun i j => raw16271step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16271step1 raw16271step0; decide +kernel
      have hl : raw16271step1Labels = raw16271step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16271step0 raw16271step0Labels permutation127 permutation3
    mixedMoment B raw16271step1 raw16271step1Labels = mixedMoment B raw16271step2 raw16271step2Labels := by
      have ha : raw16271step2 = -raw16271step1 := by apply Matrix.ext; change ∀ i j, raw16271step2 i j = -(raw16271step1 i j); unfold raw16271step2 raw16271step1; decide +kernel
      have hl : raw16271step2Labels = raw16271step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3706 node3706Labels := by rfl

def raw16272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16272Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw16272step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16272step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16272step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16272 raw16272Labels = mixedMoment B node3706 node3706Labels := by
  calc
    mixedMoment B raw16272 raw16272Labels = mixedMoment B raw16272step0 raw16272step0Labels := by
      have hz : ∀ j, raw16272 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16272step0 = (fun i j => raw16272 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16272step0 raw16272; decide +kernel
      have hl : raw16272step0Labels = raw16272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16272 raw16272Labels permutation346 hz
    mixedMoment B raw16272step0 raw16272step0Labels = mixedMoment B raw16272step1 raw16272step1Labels := by
      have ha : raw16272step1 = (fun i j => raw16272step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16272step1 raw16272step0; decide +kernel
      have hl : raw16272step1Labels = raw16272step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16272step0 raw16272step0Labels permutation127 permutation3
    mixedMoment B raw16272step1 raw16272step1Labels = mixedMoment B raw16272step2 raw16272step2Labels := by
      have ha : raw16272step2 = -raw16272step1 := by apply Matrix.ext; change ∀ i j, raw16272step2 i j = -(raw16272step1 i j); unfold raw16272step2 raw16272step1; decide +kernel
      have hl : raw16272step2Labels = raw16272step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3706 node3706Labels := by rfl

def raw16273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw16273Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1]]
def raw16273step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16273step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1]]
def raw16273step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16273step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw16273step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16273step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw16273step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16273 raw16273Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw16273 raw16273Labels = mixedMoment B raw16273step0 raw16273step0Labels := by
      have hz : ∀ j, raw16273 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16273step0 = (fun i j => raw16273 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16273step0 raw16273; decide +kernel
      have hl : raw16273step0Labels = raw16273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16273 raw16273Labels permutation434 hz
    mixedMoment B raw16273step0 raw16273step0Labels = mixedMoment B raw16273step1 raw16273step1Labels := by
      have hz : ∀ j, raw16273step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16273step1 = (fun i j => raw16273step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16273step1 raw16273step0; decide +kernel
      have hl : raw16273step1Labels = raw16273step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16273step0 raw16273step0Labels permutation80 hz
    mixedMoment B raw16273step1 raw16273step1Labels = mixedMoment B raw16273step2 raw16273step2Labels := by
      have ha : raw16273step2 = (fun i j => raw16273step1 (permutation25 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16273step2 raw16273step1; decide +kernel
      have hl : raw16273step2Labels = raw16273step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16273step1 raw16273step1Labels permutation25 permutation3
    mixedMoment B raw16273step2 raw16273step2Labels = mixedMoment B raw16273step3 raw16273step3Labels := by
      have ha : raw16273step3 = -raw16273step2 := by apply Matrix.ext; change ∀ i j, raw16273step3 i j = -(raw16273step2 i j); unfold raw16273step3 raw16273step2; decide +kernel
      have hl : raw16273step3Labels = raw16273step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3862 node3862Labels := by rfl

def raw16274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16274Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16274step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16274step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16274step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16274step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw16274step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16274step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw16274step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16274 raw16274Labels = mixedMoment B node2519 node2519Labels := by
  calc
    mixedMoment B raw16274 raw16274Labels = mixedMoment B raw16274step0 raw16274step0Labels := by
      have hz : ∀ j, raw16274 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16274step0 = (fun i j => raw16274 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16274step0 raw16274; decide +kernel
      have hl : raw16274step0Labels = raw16274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16274 raw16274Labels permutation434 hz
    mixedMoment B raw16274step0 raw16274step0Labels = mixedMoment B raw16274step1 raw16274step1Labels := by
      have hz : ∀ j, raw16274step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16274step1 = (fun i j => raw16274step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16274step1 raw16274step0; decide +kernel
      have hl : raw16274step1Labels = raw16274step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16274step0 raw16274step0Labels permutation80 hz
    mixedMoment B raw16274step1 raw16274step1Labels = mixedMoment B raw16274step2 raw16274step2Labels := by
      have ha : raw16274step2 = (fun i j => raw16274step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16274step2 raw16274step1; decide +kernel
      have hl : raw16274step2Labels = raw16274step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16274step1 raw16274step1Labels permutation31 permutation3
    mixedMoment B raw16274step2 raw16274step2Labels = mixedMoment B raw16274step3 raw16274step3Labels := by
      have ha : raw16274step3 = -raw16274step2 := by apply Matrix.ext; change ∀ i j, raw16274step3 i j = -(raw16274step2 i j); unfold raw16274step3 raw16274step2; decide +kernel
      have hl : raw16274step3Labels = raw16274step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2519 node2519Labels := by rfl

def raw16275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16275Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16275step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16275step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![3, -2, -1]]
def raw16275step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16275step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-2, 2, 0], ![-2, -1, 3]]
def raw16275step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16275step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw16275step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16275 raw16275Labels = mixedMoment B node2522 node2522Labels := by
  calc
    mixedMoment B raw16275 raw16275Labels = mixedMoment B raw16275step0 raw16275step0Labels := by
      have hz : ∀ j, raw16275 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16275step0 = (fun i j => raw16275 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16275step0 raw16275; decide +kernel
      have hl : raw16275step0Labels = raw16275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16275 raw16275Labels permutation434 hz
    mixedMoment B raw16275step0 raw16275step0Labels = mixedMoment B raw16275step1 raw16275step1Labels := by
      have hz : ∀ j, raw16275step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16275step1 = (fun i j => raw16275step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16275step1 raw16275step0; decide +kernel
      have hl : raw16275step1Labels = raw16275step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16275step0 raw16275step0Labels permutation80 hz
    mixedMoment B raw16275step1 raw16275step1Labels = mixedMoment B raw16275step2 raw16275step2Labels := by
      have ha : raw16275step2 = (fun i j => raw16275step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16275step2 raw16275step1; decide +kernel
      have hl : raw16275step2Labels = raw16275step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16275step1 raw16275step1Labels permutation30 permutation3
    mixedMoment B raw16275step2 raw16275step2Labels = mixedMoment B raw16275step3 raw16275step3Labels := by
      have ha : raw16275step3 = -raw16275step2 := by apply Matrix.ext; change ∀ i j, raw16275step3 i j = -(raw16275step2 i j); unfold raw16275step3 raw16275step2; decide +kernel
      have hl : raw16275step3Labels = raw16275step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2522 node2522Labels := by rfl

def raw16276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16276Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16276step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16276step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16276step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16276 raw16276Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw16276 raw16276Labels = mixedMoment B raw16276step0 raw16276step0Labels := by
      have hz : ∀ j, raw16276 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16276step0 = (fun i j => raw16276 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16276step0 raw16276; decide +kernel
      have hl : raw16276step0Labels = raw16276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16276 raw16276Labels permutation434 hz
    mixedMoment B raw16276step0 raw16276step0Labels = mixedMoment B raw16276step1 raw16276step1Labels := by
      have ha : raw16276step1 = (fun i j => raw16276step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16276step1 raw16276step0; decide +kernel
      have hl : raw16276step1Labels = raw16276step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16276step0 raw16276step0Labels permutation151 permutation3
    mixedMoment B raw16276step1 raw16276step1Labels = mixedMoment B raw16276step2 raw16276step2Labels := by
      have ha : raw16276step2 = -raw16276step1 := by apply Matrix.ext; change ∀ i j, raw16276step2 i j = -(raw16276step1 i j); unfold raw16276step2 raw16276step1; decide +kernel
      have hl : raw16276step2Labels = raw16276step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw16277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16277Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw16277step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16277step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16277step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16277 raw16277Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw16277 raw16277Labels = mixedMoment B raw16277step0 raw16277step0Labels := by
      have hz : ∀ j, raw16277 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16277step0 = (fun i j => raw16277 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16277step0 raw16277; decide +kernel
      have hl : raw16277step0Labels = raw16277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16277 raw16277Labels permutation346 hz
    mixedMoment B raw16277step0 raw16277step0Labels = mixedMoment B raw16277step1 raw16277step1Labels := by
      have ha : raw16277step1 = (fun i j => raw16277step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16277step1 raw16277step0; decide +kernel
      have hl : raw16277step1Labels = raw16277step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16277step0 raw16277step0Labels permutation151 permutation3
    mixedMoment B raw16277step1 raw16277step1Labels = mixedMoment B raw16277step2 raw16277step2Labels := by
      have ha : raw16277step2 = -raw16277step1 := by apply Matrix.ext; change ∀ i j, raw16277step2 i j = -(raw16277step1 i j); unfold raw16277step2 raw16277step1; decide +kernel
      have hl : raw16277step2Labels = raw16277step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw16278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw16278Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1]]
def raw16278step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16278step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1]]
def raw16278step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16278step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![3, -2, -1]]
def raw16278step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16278step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, -1, 2], ![-2, 2, 0]]
def raw16278step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16278step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw16278step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16278 raw16278Labels = mixedMoment B node2788 node2788Labels := by
  calc
    mixedMoment B raw16278 raw16278Labels = mixedMoment B raw16278step0 raw16278step0Labels := by
      have hz : ∀ j, raw16278 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw16278step0 = (fun i j => raw16278 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw16278step0 raw16278; decide +kernel
      have hl : raw16278step0Labels = raw16278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16278 raw16278Labels permutation520 hz
    mixedMoment B raw16278step0 raw16278step0Labels = mixedMoment B raw16278step1 raw16278step1Labels := by
      have hz : ∀ j, raw16278step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw16278step1 = (fun i j => raw16278step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw16278step1 raw16278step0; decide +kernel
      have hl : raw16278step1Labels = raw16278step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16278step0 raw16278step0Labels permutation104 hz
    mixedMoment B raw16278step1 raw16278step1Labels = mixedMoment B raw16278step2 raw16278step2Labels := by
      have hz : ∀ j, raw16278step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw16278step2 = (fun i j => raw16278step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw16278step2 raw16278step1; decide +kernel
      have hl : raw16278step2Labels = raw16278step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16278step1 raw16278step1Labels permutation20 hz
    mixedMoment B raw16278step2 raw16278step2Labels = mixedMoment B raw16278step3 raw16278step3Labels := by
      have ha : raw16278step3 = (fun i j => raw16278step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16278step3 raw16278step2; decide +kernel
      have hl : raw16278step3Labels = raw16278step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16278step2 raw16278step2Labels permutation7 permutation3
    mixedMoment B raw16278step3 raw16278step3Labels = mixedMoment B raw16278step4 raw16278step4Labels := by
      have ha : raw16278step4 = -raw16278step3 := by apply Matrix.ext; change ∀ i j, raw16278step4 i j = -(raw16278step3 i j); unfold raw16278step4 raw16278step3; decide +kernel
      have hl : raw16278step4Labels = raw16278step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2788 node2788Labels := by rfl

def raw16279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16279step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1]]
def raw16279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16279step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16279step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16279 raw16279Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw16279 raw16279Labels = mixedMoment B raw16279step0 raw16279step0Labels := by
      have hz : ∀ j, raw16279 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16279step0 = (fun i j => raw16279 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16279step0 raw16279; decide +kernel
      have hl : raw16279step0Labels = raw16279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16279 raw16279Labels permutation434 hz
    mixedMoment B raw16279step0 raw16279step0Labels = mixedMoment B raw16279step1 raw16279step1Labels := by
      have hz : ∀ j, raw16279step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16279step1 = (fun i j => raw16279step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16279step1 raw16279step0; decide +kernel
      have hl : raw16279step1Labels = raw16279step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16279step0 raw16279step0Labels permutation80 hz
    mixedMoment B raw16279step1 raw16279step1Labels = mixedMoment B raw16279step2 raw16279step2Labels := by
      have ha : raw16279step2 = (fun i j => raw16279step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16279step2 raw16279step1; decide +kernel
      have hl : raw16279step2Labels = raw16279step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16279step1 raw16279step1Labels permutation14 permutation2
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw16280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16280step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16280 raw16280Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw16280 raw16280Labels = mixedMoment B raw16280step0 raw16280step0Labels := by
      have hz : ∀ j, raw16280 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16280step0 = (fun i j => raw16280 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16280step0 raw16280; decide +kernel
      have hl : raw16280step0Labels = raw16280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16280 raw16280Labels permutation434 hz
    mixedMoment B raw16280step0 raw16280step0Labels = mixedMoment B raw16280step1 raw16280step1Labels := by
      have ha : raw16280step1 = (fun i j => raw16280step0 (permutation147 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16280step1 raw16280step0; decide +kernel
      have hl : raw16280step1Labels = raw16280step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16280step0 raw16280step0Labels permutation147 permutation2
    mixedMoment B raw16280step1 raw16280step1Labels = mixedMoment B raw16280step2 raw16280step2Labels := by
      have ha : raw16280step2 = -raw16280step1 := by apply Matrix.ext; change ∀ i j, raw16280step2 i j = -(raw16280step1 i j); unfold raw16280step2 raw16280step1; decide +kernel
      have hl : raw16280step2Labels = raw16280step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw16281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16281step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16281step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16281 raw16281Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw16281 raw16281Labels = mixedMoment B raw16281step0 raw16281step0Labels := by
      have hz : ∀ j, raw16281 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16281step0 = (fun i j => raw16281 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16281step0 raw16281; decide +kernel
      have hl : raw16281step0Labels = raw16281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16281 raw16281Labels permutation346 hz
    mixedMoment B raw16281step0 raw16281step0Labels = mixedMoment B raw16281step1 raw16281step1Labels := by
      have ha : raw16281step1 = (fun i j => raw16281step0 (permutation147 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16281step1 raw16281step0; decide +kernel
      have hl : raw16281step1Labels = raw16281step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16281step0 raw16281step0Labels permutation147 permutation2
    mixedMoment B raw16281step1 raw16281step1Labels = mixedMoment B raw16281step2 raw16281step2Labels := by
      have ha : raw16281step2 = -raw16281step1 := by apply Matrix.ext; change ∀ i j, raw16281step2 i j = -(raw16281step1 i j); unfold raw16281step2 raw16281step1; decide +kernel
      have hl : raw16281step2Labels = raw16281step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw16282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1]]
def raw16282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16282step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16282step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16282step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16282step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16282 raw16282Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw16282 raw16282Labels = mixedMoment B raw16282step0 raw16282step0Labels := by
      have hz : ∀ j, raw16282 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16282step0 = (fun i j => raw16282 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16282step0 raw16282; decide +kernel
      have hl : raw16282step0Labels = raw16282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16282 raw16282Labels permutation434 hz
    mixedMoment B raw16282step0 raw16282step0Labels = mixedMoment B raw16282step1 raw16282step1Labels := by
      have hz : ∀ j, raw16282step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16282step1 = (fun i j => raw16282step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16282step1 raw16282step0; decide +kernel
      have hl : raw16282step1Labels = raw16282step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16282step0 raw16282step0Labels permutation80 hz
    mixedMoment B raw16282step1 raw16282step1Labels = mixedMoment B raw16282step2 raw16282step2Labels := by
      have ha : raw16282step2 = (fun i j => raw16282step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16282step2 raw16282step1; decide +kernel
      have hl : raw16282step2Labels = raw16282step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16282step1 raw16282step1Labels permutation30 permutation2
    mixedMoment B raw16282step2 raw16282step2Labels = mixedMoment B raw16282step3 raw16282step3Labels := by
      have ha : raw16282step3 = -raw16282step2 := by apply Matrix.ext; change ∀ i j, raw16282step3 i j = -(raw16282step2 i j); unfold raw16282step3 raw16282step2; decide +kernel
      have hl : raw16282step3Labels = raw16282step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw16283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1]]
def raw16283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16283step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16283step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16283step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16283step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16283step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16283step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16283 raw16283Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw16283 raw16283Labels = mixedMoment B raw16283step0 raw16283step0Labels := by
      have hz : ∀ j, raw16283 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16283step0 = (fun i j => raw16283 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16283step0 raw16283; decide +kernel
      have hl : raw16283step0Labels = raw16283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16283 raw16283Labels permutation434 hz
    mixedMoment B raw16283step0 raw16283step0Labels = mixedMoment B raw16283step1 raw16283step1Labels := by
      have hz : ∀ j, raw16283step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16283step1 = (fun i j => raw16283step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16283step1 raw16283step0; decide +kernel
      have hl : raw16283step1Labels = raw16283step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16283step0 raw16283step0Labels permutation80 hz
    mixedMoment B raw16283step1 raw16283step1Labels = mixedMoment B raw16283step2 raw16283step2Labels := by
      have ha : raw16283step2 = (fun i j => raw16283step1 (permutation14 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16283step2 raw16283step1; decide +kernel
      have hl : raw16283step2Labels = raw16283step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16283step1 raw16283step1Labels permutation14 permutation7
    mixedMoment B raw16283step2 raw16283step2Labels = mixedMoment B raw16283step3 raw16283step3Labels := by
      have ha : raw16283step3 = -raw16283step2 := by apply Matrix.ext; change ∀ i j, raw16283step3 i j = -(raw16283step2 i j); unfold raw16283step3 raw16283step2; decide +kernel
      have hl : raw16283step3Labels = raw16283step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16283step3 raw16283step3Labels = mixedMoment B raw16283step4 raw16283step4Labels := by
      have ha : raw16283step4 = raw16283step3 := by apply Matrix.ext; unfold raw16283step4 raw16283step3; decide +kernel
      have hl : raw16283step3Labels = labelEmbedding10 ∘ raw16283step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16283step3 raw16283step3Labels raw16283step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5493 node5493Labels := by rfl

def raw16284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16284step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw16284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16284step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16284step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16284step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16284step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16284step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16284step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16284 raw16284Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw16284 raw16284Labels = mixedMoment B raw16284step0 raw16284step0Labels := by
      have hz : ∀ j, raw16284 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16284step0 = (fun i j => raw16284 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16284step0 raw16284; decide +kernel
      have hl : raw16284step0Labels = raw16284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16284 raw16284Labels permutation434 hz
    mixedMoment B raw16284step0 raw16284step0Labels = mixedMoment B raw16284step1 raw16284step1Labels := by
      have hz : ∀ j, raw16284step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16284step1 = (fun i j => raw16284step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16284step1 raw16284step0; decide +kernel
      have hl : raw16284step1Labels = raw16284step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16284step0 raw16284step0Labels permutation80 hz
    mixedMoment B raw16284step1 raw16284step1Labels = mixedMoment B raw16284step2 raw16284step2Labels := by
      have ha : raw16284step2 = (fun i j => raw16284step1 (permutation11 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16284step2 raw16284step1; decide +kernel
      have hl : raw16284step2Labels = raw16284step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16284step1 raw16284step1Labels permutation11 permutation5
    mixedMoment B raw16284step2 raw16284step2Labels = mixedMoment B raw16284step3 raw16284step3Labels := by
      have ha : raw16284step3 = -raw16284step2 := by apply Matrix.ext; change ∀ i j, raw16284step3 i j = -(raw16284step2 i j); unfold raw16284step3 raw16284step2; decide +kernel
      have hl : raw16284step3Labels = raw16284step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16284step3 raw16284step3Labels = mixedMoment B raw16284step4 raw16284step4Labels := by
      have ha : raw16284step4 = raw16284step3 := by apply Matrix.ext; unfold raw16284step4 raw16284step3; decide +kernel
      have hl : raw16284step3Labels = labelEmbedding8 ∘ raw16284step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16284step3 raw16284step3Labels raw16284step4Labels labelEmbedding8 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw16285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16285step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16285 raw16285Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw16285 raw16285Labels = mixedMoment B raw16285step0 raw16285step0Labels := by
      have hz : ∀ j, raw16285 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16285step0 = (fun i j => raw16285 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16285step0 raw16285; decide +kernel
      have hl : raw16285step0Labels = raw16285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16285 raw16285Labels permutation434 hz
    mixedMoment B raw16285step0 raw16285step0Labels = mixedMoment B raw16285step1 raw16285step1Labels := by
      have ha : raw16285step1 = (fun i j => raw16285step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16285step1 raw16285step0; decide +kernel
      have hl : raw16285step1Labels = raw16285step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16285step0 raw16285step0Labels permutation56 permutation2
    _ = mixedMoment B node5388 node5388Labels := by rfl

def raw16286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16286step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16286 raw16286Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw16286 raw16286Labels = mixedMoment B raw16286step0 raw16286step0Labels := by
      have ha : raw16286step0 = (fun i j => raw16286 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16286step0 raw16286; decide +kernel
      have hl : raw16286step0Labels = raw16286Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16286 raw16286Labels permutation202 permutation3
    mixedMoment B raw16286step0 raw16286step0Labels = mixedMoment B raw16286step1 raw16286step1Labels := by
      have ha : raw16286step1 = raw16286step0 := by apply Matrix.ext; unfold raw16286step1 raw16286step0; decide +kernel
      have hl : raw16286step0Labels = labelEmbedding6 ∘ raw16286step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16286step0 raw16286step0Labels raw16286step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw16287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16287step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16287step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16287step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16287step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16287 raw16287Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw16287 raw16287Labels = mixedMoment B raw16287step0 raw16287step0Labels := by
      have hz : ∀ j, raw16287 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16287step0 = (fun i j => raw16287 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16287step0 raw16287; decide +kernel
      have hl : raw16287step0Labels = raw16287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16287 raw16287Labels permutation434 hz
    mixedMoment B raw16287step0 raw16287step0Labels = mixedMoment B raw16287step1 raw16287step1Labels := by
      have ha : raw16287step1 = (fun i j => raw16287step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16287step1 raw16287step0; decide +kernel
      have hl : raw16287step1Labels = raw16287step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16287step0 raw16287step0Labels permutation44 permutation5
    mixedMoment B raw16287step1 raw16287step1Labels = mixedMoment B raw16287step2 raw16287step2Labels := by
      have ha : raw16287step2 = -raw16287step1 := by apply Matrix.ext; change ∀ i j, raw16287step2 i j = -(raw16287step1 i j); unfold raw16287step2 raw16287step1; decide +kernel
      have hl : raw16287step2Labels = raw16287step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16287step2 raw16287step2Labels = mixedMoment B raw16287step3 raw16287step3Labels := by
      have ha : raw16287step3 = raw16287step2 := by apply Matrix.ext; unfold raw16287step3 raw16287step2; decide +kernel
      have hl : raw16287step2Labels = labelEmbedding8 ∘ raw16287step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16287step2 raw16287step2Labels raw16287step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw16288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16288step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16288step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16288step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16288 raw16288Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw16288 raw16288Labels = mixedMoment B raw16288step0 raw16288step0Labels := by
      have hz : ∀ j, raw16288 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16288step0 = (fun i j => raw16288 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16288step0 raw16288; decide +kernel
      have hl : raw16288step0Labels = raw16288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16288 raw16288Labels permutation434 hz
    mixedMoment B raw16288step0 raw16288step0Labels = mixedMoment B raw16288step1 raw16288step1Labels := by
      have ha : raw16288step1 = (fun i j => raw16288step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16288step1 raw16288step0; decide +kernel
      have hl : raw16288step1Labels = raw16288step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16288step0 raw16288step0Labels permutation35 permutation3
    mixedMoment B raw16288step1 raw16288step1Labels = mixedMoment B raw16288step2 raw16288step2Labels := by
      have ha : raw16288step2 = raw16288step1 := by apply Matrix.ext; unfold raw16288step2 raw16288step1; decide +kernel
      have hl : raw16288step1Labels = labelEmbedding6 ∘ raw16288step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16288step1 raw16288step1Labels raw16288step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw16289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16289step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16289step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16289 raw16289Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw16289 raw16289Labels = mixedMoment B raw16289step0 raw16289step0Labels := by
      have hz : ∀ j, raw16289 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16289step0 = (fun i j => raw16289 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16289step0 raw16289; decide +kernel
      have hl : raw16289step0Labels = raw16289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16289 raw16289Labels permutation346 hz
    mixedMoment B raw16289step0 raw16289step0Labels = mixedMoment B raw16289step1 raw16289step1Labels := by
      have ha : raw16289step1 = (fun i j => raw16289step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16289step1 raw16289step0; decide +kernel
      have hl : raw16289step1Labels = raw16289step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16289step0 raw16289step0Labels permutation56 permutation2
    _ = mixedMoment B node5388 node5388Labels := by rfl

def raw16290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16290step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16290step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16290step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16290 raw16290Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw16290 raw16290Labels = mixedMoment B raw16290step0 raw16290step0Labels := by
      have ha : raw16290step0 = (fun i j => raw16290 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16290step0 raw16290; decide +kernel
      have hl : raw16290step0Labels = raw16290Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16290 raw16290Labels permutation178 permutation3
    mixedMoment B raw16290step0 raw16290step0Labels = mixedMoment B raw16290step1 raw16290step1Labels := by
      have ha : raw16290step1 = raw16290step0 := by apply Matrix.ext; unfold raw16290step1 raw16290step0; decide +kernel
      have hl : raw16290step0Labels = labelEmbedding6 ∘ raw16290step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16290step0 raw16290step0Labels raw16290step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw16291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16291step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16291step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16291step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16291step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16291 raw16291Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw16291 raw16291Labels = mixedMoment B raw16291step0 raw16291step0Labels := by
      have hz : ∀ j, raw16291 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16291step0 = (fun i j => raw16291 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16291step0 raw16291; decide +kernel
      have hl : raw16291step0Labels = raw16291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16291 raw16291Labels permutation346 hz
    mixedMoment B raw16291step0 raw16291step0Labels = mixedMoment B raw16291step1 raw16291step1Labels := by
      have ha : raw16291step1 = (fun i j => raw16291step0 (permutation44 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16291step1 raw16291step0; decide +kernel
      have hl : raw16291step1Labels = raw16291step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16291step0 raw16291step0Labels permutation44 permutation5
    mixedMoment B raw16291step1 raw16291step1Labels = mixedMoment B raw16291step2 raw16291step2Labels := by
      have ha : raw16291step2 = -raw16291step1 := by apply Matrix.ext; change ∀ i j, raw16291step2 i j = -(raw16291step1 i j); unfold raw16291step2 raw16291step1; decide +kernel
      have hl : raw16291step2Labels = raw16291step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16291step2 raw16291step2Labels = mixedMoment B raw16291step3 raw16291step3Labels := by
      have ha : raw16291step3 = raw16291step2 := by apply Matrix.ext; unfold raw16291step3 raw16291step2; decide +kernel
      have hl : raw16291step2Labels = labelEmbedding8 ∘ raw16291step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16291step2 raw16291step2Labels raw16291step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw16292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16292step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16292step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16292 raw16292Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw16292 raw16292Labels = mixedMoment B raw16292step0 raw16292step0Labels := by
      have hz : ∀ j, raw16292 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16292step0 = (fun i j => raw16292 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16292step0 raw16292; decide +kernel
      have hl : raw16292step0Labels = raw16292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16292 raw16292Labels permutation346 hz
    mixedMoment B raw16292step0 raw16292step0Labels = mixedMoment B raw16292step1 raw16292step1Labels := by
      have ha : raw16292step1 = (fun i j => raw16292step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16292step1 raw16292step0; decide +kernel
      have hl : raw16292step1Labels = raw16292step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16292step0 raw16292step0Labels permutation35 permutation3
    mixedMoment B raw16292step1 raw16292step1Labels = mixedMoment B raw16292step2 raw16292step2Labels := by
      have ha : raw16292step2 = raw16292step1 := by apply Matrix.ext; unfold raw16292step2 raw16292step1; decide +kernel
      have hl : raw16292step1Labels = labelEmbedding6 ∘ raw16292step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16292step1 raw16292step1Labels raw16292step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw16293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16293step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![2, -1, -1]]
def raw16293step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16293step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16293step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16293 raw16293Labels = mixedMoment B node5390 node5390Labels := by
  calc
    mixedMoment B raw16293 raw16293Labels = mixedMoment B raw16293step0 raw16293step0Labels := by
      have hz : ∀ j, raw16293 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16293step0 = (fun i j => raw16293 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16293step0 raw16293; decide +kernel
      have hl : raw16293step0Labels = raw16293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16293 raw16293Labels permutation434 hz
    mixedMoment B raw16293step0 raw16293step0Labels = mixedMoment B raw16293step1 raw16293step1Labels := by
      have hz : ∀ j, raw16293step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16293step1 = (fun i j => raw16293step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16293step1 raw16293step0; decide +kernel
      have hl : raw16293step1Labels = raw16293step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16293step0 raw16293step0Labels permutation80 hz
    mixedMoment B raw16293step1 raw16293step1Labels = mixedMoment B raw16293step2 raw16293step2Labels := by
      have ha : raw16293step2 = (fun i j => raw16293step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16293step2 raw16293step1; decide +kernel
      have hl : raw16293step2Labels = raw16293step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16293step1 raw16293step1Labels permutation14 permutation2
    _ = mixedMoment B node5390 node5390Labels := by rfl

def raw16294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16294step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16294step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16294 raw16294Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw16294 raw16294Labels = mixedMoment B raw16294step0 raw16294step0Labels := by
      have hz : ∀ j, raw16294 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16294step0 = (fun i j => raw16294 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16294step0 raw16294; decide +kernel
      have hl : raw16294step0Labels = raw16294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16294 raw16294Labels permutation434 hz
    mixedMoment B raw16294step0 raw16294step0Labels = mixedMoment B raw16294step1 raw16294step1Labels := by
      have ha : raw16294step1 = (fun i j => raw16294step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16294step1 raw16294step0; decide +kernel
      have hl : raw16294step1Labels = raw16294step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16294step0 raw16294step0Labels permutation38 permutation3
    mixedMoment B raw16294step1 raw16294step1Labels = mixedMoment B raw16294step2 raw16294step2Labels := by
      have ha : raw16294step2 = raw16294step1 := by apply Matrix.ext; unfold raw16294step2 raw16294step1; decide +kernel
      have hl : raw16294step1Labels = labelEmbedding6 ∘ raw16294step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16294step1 raw16294step1Labels raw16294step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw16295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16295step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16295step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16295step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16295step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16295 raw16295Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw16295 raw16295Labels = mixedMoment B raw16295step0 raw16295step0Labels := by
      have hz : ∀ j, raw16295 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16295step0 = (fun i j => raw16295 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16295step0 raw16295; decide +kernel
      have hl : raw16295step0Labels = raw16295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16295 raw16295Labels permutation346 hz
    mixedMoment B raw16295step0 raw16295step0Labels = mixedMoment B raw16295step1 raw16295step1Labels := by
      have ha : raw16295step1 = (fun i j => raw16295step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16295step1 raw16295step0; decide +kernel
      have hl : raw16295step1Labels = raw16295step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16295step0 raw16295step0Labels permutation38 permutation3
    mixedMoment B raw16295step1 raw16295step1Labels = mixedMoment B raw16295step2 raw16295step2Labels := by
      have ha : raw16295step2 = raw16295step1 := by apply Matrix.ext; unfold raw16295step2 raw16295step1; decide +kernel
      have hl : raw16295step1Labels = labelEmbedding6 ∘ raw16295step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16295step1 raw16295step1Labels raw16295step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw16296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw16296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw16296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16296step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1]]
def raw16296step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16296step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16296step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16296step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16296step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16296 raw16296Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw16296 raw16296Labels = mixedMoment B raw16296step0 raw16296step0Labels := by
      have hz : ∀ j, raw16296 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16296step0 = (fun i j => raw16296 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16296step0 raw16296; decide +kernel
      have hl : raw16296step0Labels = raw16296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16296 raw16296Labels permutation434 hz
    mixedMoment B raw16296step0 raw16296step0Labels = mixedMoment B raw16296step1 raw16296step1Labels := by
      have hz : ∀ j, raw16296step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16296step1 = (fun i j => raw16296step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16296step1 raw16296step0; decide +kernel
      have hl : raw16296step1Labels = raw16296step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16296step0 raw16296step0Labels permutation80 hz
    mixedMoment B raw16296step1 raw16296step1Labels = mixedMoment B raw16296step2 raw16296step2Labels := by
      have ha : raw16296step2 = (fun i j => raw16296step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16296step2 raw16296step1; decide +kernel
      have hl : raw16296step2Labels = raw16296step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16296step1 raw16296step1Labels permutation9 permutation3
    mixedMoment B raw16296step2 raw16296step2Labels = mixedMoment B raw16296step3 raw16296step3Labels := by
      have ha : raw16296step3 = raw16296step2 := by apply Matrix.ext; unfold raw16296step3 raw16296step2; decide +kernel
      have hl : raw16296step2Labels = labelEmbedding6 ∘ raw16296step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16296step2 raw16296step2Labels raw16296step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw16297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![3, -2, -1]]
def raw16297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw16297step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16297step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw16297step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16297step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw16297step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16297 raw16297Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw16297 raw16297Labels = mixedMoment B raw16297step0 raw16297step0Labels := by
      have hz : ∀ j, raw16297 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16297step0 = (fun i j => raw16297 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16297step0 raw16297; decide +kernel
      have hl : raw16297step0Labels = raw16297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16297 raw16297Labels permutation434 hz
    mixedMoment B raw16297step0 raw16297step0Labels = mixedMoment B raw16297step1 raw16297step1Labels := by
      have hz : ∀ j, raw16297step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16297step1 = (fun i j => raw16297step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16297step1 raw16297step0; decide +kernel
      have hl : raw16297step1Labels = raw16297step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16297step0 raw16297step0Labels permutation80 hz
    mixedMoment B raw16297step1 raw16297step1Labels = mixedMoment B raw16297step2 raw16297step2Labels := by
      have ha : raw16297step2 = (fun i j => raw16297step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16297step2 raw16297step1; decide +kernel
      have hl : raw16297step2Labels = raw16297step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16297step1 raw16297step1Labels permutation31 permutation3
    mixedMoment B raw16297step2 raw16297step2Labels = mixedMoment B raw16297step3 raw16297step3Labels := by
      have ha : raw16297step3 = -raw16297step2 := by apply Matrix.ext; change ∀ i j, raw16297step3 i j = -(raw16297step2 i j); unfold raw16297step3 raw16297step2; decide +kernel
      have hl : raw16297step3Labels = raw16297step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16297step3 raw16297step3Labels = mixedMoment B raw16297step4 raw16297step4Labels := by
      have ha : raw16297step4 = raw16297step3 := by apply Matrix.ext; unfold raw16297step4 raw16297step3; decide +kernel
      have hl : raw16297step3Labels = labelEmbedding6 ∘ raw16297step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16297step3 raw16297step3Labels raw16297step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5176 node5176Labels := by rfl

def raw16298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16298step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16298step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16298step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16298step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16298step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16298 raw16298Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw16298 raw16298Labels = mixedMoment B raw16298step0 raw16298step0Labels := by
      have hz : ∀ j, raw16298 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16298step0 = (fun i j => raw16298 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16298step0 raw16298; decide +kernel
      have hl : raw16298step0Labels = raw16298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16298 raw16298Labels permutation434 hz
    mixedMoment B raw16298step0 raw16298step0Labels = mixedMoment B raw16298step1 raw16298step1Labels := by
      have ha : raw16298step1 = (fun i j => raw16298step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16298step1 raw16298step0; decide +kernel
      have hl : raw16298step1Labels = raw16298step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16298step0 raw16298step0Labels permutation149 permutation3
    mixedMoment B raw16298step1 raw16298step1Labels = mixedMoment B raw16298step2 raw16298step2Labels := by
      have ha : raw16298step2 = -raw16298step1 := by apply Matrix.ext; change ∀ i j, raw16298step2 i j = -(raw16298step1 i j); unfold raw16298step2 raw16298step1; decide +kernel
      have hl : raw16298step2Labels = raw16298step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16298step2 raw16298step2Labels = mixedMoment B raw16298step3 raw16298step3Labels := by
      have ha : raw16298step3 = raw16298step2 := by apply Matrix.ext; unfold raw16298step3 raw16298step2; decide +kernel
      have hl : raw16298step2Labels = labelEmbedding6 ∘ raw16298step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16298step2 raw16298step2Labels raw16298step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw16299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16299step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16299step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16299step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16299step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16299step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16299step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16299 raw16299Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw16299 raw16299Labels = mixedMoment B raw16299step0 raw16299step0Labels := by
      have hz : ∀ j, raw16299 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16299step0 = (fun i j => raw16299 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16299step0 raw16299; decide +kernel
      have hl : raw16299step0Labels = raw16299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16299 raw16299Labels permutation346 hz
    mixedMoment B raw16299step0 raw16299step0Labels = mixedMoment B raw16299step1 raw16299step1Labels := by
      have ha : raw16299step1 = (fun i j => raw16299step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16299step1 raw16299step0; decide +kernel
      have hl : raw16299step1Labels = raw16299step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16299step0 raw16299step0Labels permutation149 permutation3
    mixedMoment B raw16299step1 raw16299step1Labels = mixedMoment B raw16299step2 raw16299step2Labels := by
      have ha : raw16299step2 = -raw16299step1 := by apply Matrix.ext; change ∀ i j, raw16299step2 i j = -(raw16299step1 i j); unfold raw16299step2 raw16299step1; decide +kernel
      have hl : raw16299step2Labels = raw16299step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16299step2 raw16299step2Labels = mixedMoment B raw16299step3 raw16299step3Labels := by
      have ha : raw16299step3 = raw16299step2 := by apply Matrix.ext; unfold raw16299step3 raw16299step2; decide +kernel
      have hl : raw16299step2Labels = labelEmbedding6 ∘ raw16299step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16299step2 raw16299step2Labels raw16299step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw16300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw16300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw16300step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16300step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw16300step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16300step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw16300step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16300step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16300step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16300step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16300step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16300 raw16300Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw16300 raw16300Labels = mixedMoment B raw16300step0 raw16300step0Labels := by
      have hz : ∀ j, raw16300 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16300step0 = (fun i j => raw16300 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16300step0 raw16300; decide +kernel
      have hl : raw16300step0Labels = raw16300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16300 raw16300Labels permutation434 hz
    mixedMoment B raw16300step0 raw16300step0Labels = mixedMoment B raw16300step1 raw16300step1Labels := by
      have hz : ∀ j, raw16300step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16300step1 = (fun i j => raw16300step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16300step1 raw16300step0; decide +kernel
      have hl : raw16300step1Labels = raw16300step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16300step0 raw16300step0Labels permutation80 hz
    mixedMoment B raw16300step1 raw16300step1Labels = mixedMoment B raw16300step2 raw16300step2Labels := by
      have ha : raw16300step2 = (fun i j => raw16300step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16300step2 raw16300step1; decide +kernel
      have hl : raw16300step2Labels = raw16300step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16300step1 raw16300step1Labels permutation31 permutation3
    mixedMoment B raw16300step2 raw16300step2Labels = mixedMoment B raw16300step3 raw16300step3Labels := by
      have ha : raw16300step3 = -raw16300step2 := by apply Matrix.ext; change ∀ i j, raw16300step3 i j = -(raw16300step2 i j); unfold raw16300step3 raw16300step2; decide +kernel
      have hl : raw16300step3Labels = raw16300step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16300step3 raw16300step3Labels = mixedMoment B raw16300step4 raw16300step4Labels := by
      have ha : raw16300step4 = raw16300step3 := by apply Matrix.ext; unfold raw16300step4 raw16300step3; decide +kernel
      have hl : raw16300step3Labels = labelEmbedding6 ∘ raw16300step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16300step3 raw16300step3Labels raw16300step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw16301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1]]
def raw16301step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16301step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw16301step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16301step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw16301step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16301 raw16301Labels = mixedMoment B node4001 node4001Labels := by
  calc
    mixedMoment B raw16301 raw16301Labels = mixedMoment B raw16301step0 raw16301step0Labels := by
      have hz : ∀ j, raw16301 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16301step0 = (fun i j => raw16301 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16301step0 raw16301; decide +kernel
      have hl : raw16301step0Labels = raw16301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16301 raw16301Labels permutation434 hz
    mixedMoment B raw16301step0 raw16301step0Labels = mixedMoment B raw16301step1 raw16301step1Labels := by
      have hz : ∀ j, raw16301step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16301step1 = (fun i j => raw16301step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16301step1 raw16301step0; decide +kernel
      have hl : raw16301step1Labels = raw16301step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16301step0 raw16301step0Labels permutation80 hz
    mixedMoment B raw16301step1 raw16301step1Labels = mixedMoment B raw16301step2 raw16301step2Labels := by
      have ha : raw16301step2 = (fun i j => raw16301step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16301step2 raw16301step1; decide +kernel
      have hl : raw16301step2Labels = raw16301step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16301step1 raw16301step1Labels permutation30 permutation3
    mixedMoment B raw16301step2 raw16301step2Labels = mixedMoment B raw16301step3 raw16301step3Labels := by
      have ha : raw16301step3 = -raw16301step2 := by apply Matrix.ext; change ∀ i j, raw16301step3 i j = -(raw16301step2 i j); unfold raw16301step3 raw16301step2; decide +kernel
      have hl : raw16301step3Labels = raw16301step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4001 node4001Labels := by rfl

def raw16302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16302step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16302step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16302step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16302step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16302 raw16302Labels = mixedMoment B node3998 node3998Labels := by
  calc
    mixedMoment B raw16302 raw16302Labels = mixedMoment B raw16302step0 raw16302step0Labels := by
      have hz : ∀ j, raw16302 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16302step0 = (fun i j => raw16302 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16302step0 raw16302; decide +kernel
      have hl : raw16302step0Labels = raw16302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16302 raw16302Labels permutation434 hz
    mixedMoment B raw16302step0 raw16302step0Labels = mixedMoment B raw16302step1 raw16302step1Labels := by
      have ha : raw16302step1 = (fun i j => raw16302step0 (permutation148 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16302step1 raw16302step0; decide +kernel
      have hl : raw16302step1Labels = raw16302step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16302step0 raw16302step0Labels permutation148 permutation3
    mixedMoment B raw16302step1 raw16302step1Labels = mixedMoment B raw16302step2 raw16302step2Labels := by
      have ha : raw16302step2 = -raw16302step1 := by apply Matrix.ext; change ∀ i j, raw16302step2 i j = -(raw16302step1 i j); unfold raw16302step2 raw16302step1; decide +kernel
      have hl : raw16302step2Labels = raw16302step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3998 node3998Labels := by rfl

def raw16303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16303step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw16303step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16303step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16303step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16303 raw16303Labels = mixedMoment B node3998 node3998Labels := by
  calc
    mixedMoment B raw16303 raw16303Labels = mixedMoment B raw16303step0 raw16303step0Labels := by
      have hz : ∀ j, raw16303 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16303step0 = (fun i j => raw16303 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16303step0 raw16303; decide +kernel
      have hl : raw16303step0Labels = raw16303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16303 raw16303Labels permutation346 hz
    mixedMoment B raw16303step0 raw16303step0Labels = mixedMoment B raw16303step1 raw16303step1Labels := by
      have ha : raw16303step1 = (fun i j => raw16303step0 (permutation148 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16303step1 raw16303step0; decide +kernel
      have hl : raw16303step1Labels = raw16303step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16303step0 raw16303step0Labels permutation148 permutation3
    mixedMoment B raw16303step1 raw16303step1Labels = mixedMoment B raw16303step2 raw16303step2Labels := by
      have ha : raw16303step2 = -raw16303step1 := by apply Matrix.ext; change ∀ i j, raw16303step2 i j = -(raw16303step1 i j); unfold raw16303step2 raw16303step1; decide +kernel
      have hl : raw16303step2Labels = raw16303step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3998 node3998Labels := by rfl

def raw16304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16304Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16304step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1]]
def raw16304step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16304step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw16304step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16304step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16304step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16304 raw16304Labels = mixedMoment B node4017 node4017Labels := by
  calc
    mixedMoment B raw16304 raw16304Labels = mixedMoment B raw16304step0 raw16304step0Labels := by
      have hz : ∀ j, raw16304 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16304step0 = (fun i j => raw16304 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16304step0 raw16304; decide +kernel
      have hl : raw16304step0Labels = raw16304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16304 raw16304Labels permutation434 hz
    mixedMoment B raw16304step0 raw16304step0Labels = mixedMoment B raw16304step1 raw16304step1Labels := by
      have hz : ∀ j, raw16304step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16304step1 = (fun i j => raw16304step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16304step1 raw16304step0; decide +kernel
      have hl : raw16304step1Labels = raw16304step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16304step0 raw16304step0Labels permutation80 hz
    mixedMoment B raw16304step1 raw16304step1Labels = mixedMoment B raw16304step2 raw16304step2Labels := by
      have ha : raw16304step2 = (fun i j => raw16304step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16304step2 raw16304step1; decide +kernel
      have hl : raw16304step2Labels = raw16304step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16304step1 raw16304step1Labels permutation31 permutation3
    mixedMoment B raw16304step2 raw16304step2Labels = mixedMoment B raw16304step3 raw16304step3Labels := by
      have ha : raw16304step3 = -raw16304step2 := by apply Matrix.ext; change ∀ i j, raw16304step3 i j = -(raw16304step2 i j); unfold raw16304step3 raw16304step2; decide +kernel
      have hl : raw16304step3Labels = raw16304step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4017 node4017Labels := by rfl

def raw16305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16305Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16305step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16305step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1]]
def raw16305step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16305step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw16305step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16305step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw16305step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16305 raw16305Labels = mixedMoment B node4018 node4018Labels := by
  calc
    mixedMoment B raw16305 raw16305Labels = mixedMoment B raw16305step0 raw16305step0Labels := by
      have hz : ∀ j, raw16305 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16305step0 = (fun i j => raw16305 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16305step0 raw16305; decide +kernel
      have hl : raw16305step0Labels = raw16305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16305 raw16305Labels permutation434 hz
    mixedMoment B raw16305step0 raw16305step0Labels = mixedMoment B raw16305step1 raw16305step1Labels := by
      have hz : ∀ j, raw16305step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16305step1 = (fun i j => raw16305step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16305step1 raw16305step0; decide +kernel
      have hl : raw16305step1Labels = raw16305step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16305step0 raw16305step0Labels permutation80 hz
    mixedMoment B raw16305step1 raw16305step1Labels = mixedMoment B raw16305step2 raw16305step2Labels := by
      have ha : raw16305step2 = (fun i j => raw16305step1 (permutation14 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16305step2 raw16305step1; decide +kernel
      have hl : raw16305step2Labels = raw16305step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16305step1 raw16305step1Labels permutation14 permutation6
    mixedMoment B raw16305step2 raw16305step2Labels = mixedMoment B raw16305step3 raw16305step3Labels := by
      have ha : raw16305step3 = -raw16305step2 := by apply Matrix.ext; change ∀ i j, raw16305step3 i j = -(raw16305step2 i j); unfold raw16305step3 raw16305step2; decide +kernel
      have hl : raw16305step3Labels = raw16305step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4018 node4018Labels := by rfl

def raw16306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16306Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16306step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16306step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw16306step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16306step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16306 raw16306Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw16306 raw16306Labels = mixedMoment B raw16306step0 raw16306step0Labels := by
      have hz : ∀ j, raw16306 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16306step0 = (fun i j => raw16306 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16306step0 raw16306; decide +kernel
      have hl : raw16306step0Labels = raw16306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16306 raw16306Labels permutation434 hz
    mixedMoment B raw16306step0 raw16306step0Labels = mixedMoment B raw16306step1 raw16306step1Labels := by
      have hz : ∀ j, raw16306step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16306step1 = (fun i j => raw16306step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16306step1 raw16306step0; decide +kernel
      have hl : raw16306step1Labels = raw16306step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16306step0 raw16306step0Labels permutation80 hz
    mixedMoment B raw16306step1 raw16306step1Labels = mixedMoment B raw16306step2 raw16306step2Labels := by
      have ha : raw16306step2 = (fun i j => raw16306step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16306step2 raw16306step1; decide +kernel
      have hl : raw16306step2Labels = raw16306step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16306step1 raw16306step1Labels permutation8 permutation3
    _ = mixedMoment B node2278 node2278Labels := by rfl

def raw16307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16307Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16307step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16307step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16307 raw16307Labels = mixedMoment B node3737 node3737Labels := by
  calc
    mixedMoment B raw16307 raw16307Labels = mixedMoment B raw16307step0 raw16307step0Labels := by
      have hz : ∀ j, raw16307 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16307step0 = (fun i j => raw16307 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16307step0 raw16307; decide +kernel
      have hl : raw16307step0Labels = raw16307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16307 raw16307Labels permutation434 hz
    mixedMoment B raw16307step0 raw16307step0Labels = mixedMoment B raw16307step1 raw16307step1Labels := by
      have ha : raw16307step1 = (fun i j => raw16307step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16307step1 raw16307step0; decide +kernel
      have hl : raw16307step1Labels = raw16307step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16307step0 raw16307step0Labels permutation34 permutation3
    _ = mixedMoment B node3737 node3737Labels := by rfl

def raw16308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16308Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16308 raw16308Labels = mixedMoment B node3787 node3787Labels := by
  calc
    mixedMoment B raw16308 raw16308Labels = mixedMoment B raw16308step0 raw16308step0Labels := by
      have ha : raw16308step0 = (fun i j => raw16308 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16308step0 raw16308; decide +kernel
      have hl : raw16308step0Labels = raw16308Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16308 raw16308Labels permutation202 permutation3
    _ = mixedMoment B node3787 node3787Labels := by rfl

def raw16309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16309Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16309step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16309 raw16309Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw16309 raw16309Labels = mixedMoment B raw16309step0 raw16309step0Labels := by
      have hz : ∀ j, raw16309 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16309step0 = (fun i j => raw16309 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16309step0 raw16309; decide +kernel
      have hl : raw16309step0Labels = raw16309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16309 raw16309Labels permutation434 hz
    mixedMoment B raw16309step0 raw16309step0Labels = mixedMoment B raw16309step1 raw16309step1Labels := by
      have ha : raw16309step1 = (fun i j => raw16309step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16309step1 raw16309step0; decide +kernel
      have hl : raw16309step1Labels = raw16309step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16309step0 raw16309step0Labels permutation34 permutation3
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw16310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16310Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16310step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16310step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16310 raw16310Labels = mixedMoment B node3887 node3887Labels := by
  calc
    mixedMoment B raw16310 raw16310Labels = mixedMoment B raw16310step0 raw16310step0Labels := by
      have hz : ∀ j, raw16310 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16310step0 = (fun i j => raw16310 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16310step0 raw16310; decide +kernel
      have hl : raw16310step0Labels = raw16310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16310 raw16310Labels permutation434 hz
    mixedMoment B raw16310step0 raw16310step0Labels = mixedMoment B raw16310step1 raw16310step1Labels := by
      have ha : raw16310step1 = (fun i j => raw16310step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16310step1 raw16310step0; decide +kernel
      have hl : raw16310step1Labels = raw16310step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16310step0 raw16310step0Labels permutation35 permutation3
    _ = mixedMoment B node3887 node3887Labels := by rfl

def raw16311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16311Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16311step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16311 raw16311Labels = mixedMoment B node3737 node3737Labels := by
  calc
    mixedMoment B raw16311 raw16311Labels = mixedMoment B raw16311step0 raw16311step0Labels := by
      have hz : ∀ j, raw16311 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16311step0 = (fun i j => raw16311 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16311step0 raw16311; decide +kernel
      have hl : raw16311step0Labels = raw16311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16311 raw16311Labels permutation346 hz
    mixedMoment B raw16311step0 raw16311step0Labels = mixedMoment B raw16311step1 raw16311step1Labels := by
      have ha : raw16311step1 = (fun i j => raw16311step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16311step1 raw16311step0; decide +kernel
      have hl : raw16311step1Labels = raw16311step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16311step0 raw16311step0Labels permutation34 permutation3
    _ = mixedMoment B node3737 node3737Labels := by rfl

def raw16312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16312Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16312 raw16312Labels = mixedMoment B node3787 node3787Labels := by
  calc
    mixedMoment B raw16312 raw16312Labels = mixedMoment B raw16312step0 raw16312step0Labels := by
      have ha : raw16312step0 = (fun i j => raw16312 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16312step0 raw16312; decide +kernel
      have hl : raw16312step0Labels = raw16312Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16312 raw16312Labels permutation178 permutation3
    _ = mixedMoment B node3787 node3787Labels := by rfl

def raw16313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16313Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw16313step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16313step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16313 raw16313Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw16313 raw16313Labels = mixedMoment B raw16313step0 raw16313step0Labels := by
      have hz : ∀ j, raw16313 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16313step0 = (fun i j => raw16313 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16313step0 raw16313; decide +kernel
      have hl : raw16313step0Labels = raw16313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16313 raw16313Labels permutation346 hz
    mixedMoment B raw16313step0 raw16313step0Labels = mixedMoment B raw16313step1 raw16313step1Labels := by
      have ha : raw16313step1 = (fun i j => raw16313step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16313step1 raw16313step0; decide +kernel
      have hl : raw16313step1Labels = raw16313step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16313step0 raw16313step0Labels permutation34 permutation3
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw16314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16314Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16314step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16314step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16314 raw16314Labels = mixedMoment B node3887 node3887Labels := by
  calc
    mixedMoment B raw16314 raw16314Labels = mixedMoment B raw16314step0 raw16314step0Labels := by
      have hz : ∀ j, raw16314 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16314step0 = (fun i j => raw16314 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16314step0 raw16314; decide +kernel
      have hl : raw16314step0Labels = raw16314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16314 raw16314Labels permutation346 hz
    mixedMoment B raw16314step0 raw16314step0Labels = mixedMoment B raw16314step1 raw16314step1Labels := by
      have ha : raw16314step1 = (fun i j => raw16314step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16314step1 raw16314step0; decide +kernel
      have hl : raw16314step1Labels = raw16314step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16314step0 raw16314step0Labels permutation35 permutation3
    _ = mixedMoment B node3887 node3887Labels := by rfl

def raw16315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16315Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16315step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16315step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![2, -1, -1]]
def raw16315step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16315step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16315step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16315 raw16315Labels = mixedMoment B node3741 node3741Labels := by
  calc
    mixedMoment B raw16315 raw16315Labels = mixedMoment B raw16315step0 raw16315step0Labels := by
      have hz : ∀ j, raw16315 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16315step0 = (fun i j => raw16315 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16315step0 raw16315; decide +kernel
      have hl : raw16315step0Labels = raw16315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16315 raw16315Labels permutation434 hz
    mixedMoment B raw16315step0 raw16315step0Labels = mixedMoment B raw16315step1 raw16315step1Labels := by
      have hz : ∀ j, raw16315step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16315step1 = (fun i j => raw16315step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16315step1 raw16315step0; decide +kernel
      have hl : raw16315step1Labels = raw16315step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16315step0 raw16315step0Labels permutation80 hz
    mixedMoment B raw16315step1 raw16315step1Labels = mixedMoment B raw16315step2 raw16315step2Labels := by
      have ha : raw16315step2 = (fun i j => raw16315step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16315step2 raw16315step1; decide +kernel
      have hl : raw16315step2Labels = raw16315step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16315step1 raw16315step1Labels permutation8 permutation3
    _ = mixedMoment B node3741 node3741Labels := by rfl

def raw16316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16316Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16316step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16316 raw16316Labels = mixedMoment B node3790 node3790Labels := by
  calc
    mixedMoment B raw16316 raw16316Labels = mixedMoment B raw16316step0 raw16316step0Labels := by
      have hz : ∀ j, raw16316 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16316step0 = (fun i j => raw16316 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16316step0 raw16316; decide +kernel
      have hl : raw16316step0Labels = raw16316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16316 raw16316Labels permutation434 hz
    mixedMoment B raw16316step0 raw16316step0Labels = mixedMoment B raw16316step1 raw16316step1Labels := by
      have ha : raw16316step1 = (fun i j => raw16316step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16316step1 raw16316step0; decide +kernel
      have hl : raw16316step1Labels = raw16316step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16316step0 raw16316step0Labels permutation38 permutation3
    _ = mixedMoment B node3790 node3790Labels := by rfl

def raw16317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16317Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw16317step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw16317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16317 raw16317Labels = mixedMoment B node3790 node3790Labels := by
  calc
    mixedMoment B raw16317 raw16317Labels = mixedMoment B raw16317step0 raw16317step0Labels := by
      have hz : ∀ j, raw16317 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16317step0 = (fun i j => raw16317 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16317step0 raw16317; decide +kernel
      have hl : raw16317step0Labels = raw16317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16317 raw16317Labels permutation346 hz
    mixedMoment B raw16317step0 raw16317step0Labels = mixedMoment B raw16317step1 raw16317step1Labels := by
      have ha : raw16317step1 = (fun i j => raw16317step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16317step1 raw16317step0; decide +kernel
      have hl : raw16317step1Labels = raw16317step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16317step0 raw16317step0Labels permutation38 permutation3
    _ = mixedMoment B node3790 node3790Labels := by rfl

def raw16318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw16318Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw16318step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16318step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1]]
def raw16318step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16318step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw16318step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16318 raw16318Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw16318 raw16318Labels = mixedMoment B raw16318step0 raw16318step0Labels := by
      have hz : ∀ j, raw16318 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16318step0 = (fun i j => raw16318 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16318step0 raw16318; decide +kernel
      have hl : raw16318step0Labels = raw16318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16318 raw16318Labels permutation434 hz
    mixedMoment B raw16318step0 raw16318step0Labels = mixedMoment B raw16318step1 raw16318step1Labels := by
      have hz : ∀ j, raw16318step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16318step1 = (fun i j => raw16318step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16318step1 raw16318step0; decide +kernel
      have hl : raw16318step1Labels = raw16318step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16318step0 raw16318step0Labels permutation80 hz
    mixedMoment B raw16318step1 raw16318step1Labels = mixedMoment B raw16318step2 raw16318step2Labels := by
      have ha : raw16318step2 = (fun i j => raw16318step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16318step2 raw16318step1; decide +kernel
      have hl : raw16318step2Labels = raw16318step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16318step1 raw16318step1Labels permutation9 permutation3
    _ = mixedMoment B node3888 node3888Labels := by rfl

def raw16319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16319Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16319step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16319step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![3, -2, -1]]
def raw16319step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16319step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw16319step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16319step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw16319step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16319 raw16319Labels = mixedMoment B node2604 node2604Labels := by
  calc
    mixedMoment B raw16319 raw16319Labels = mixedMoment B raw16319step0 raw16319step0Labels := by
      have hz : ∀ j, raw16319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16319step0 = (fun i j => raw16319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16319step0 raw16319; decide +kernel
      have hl : raw16319step0Labels = raw16319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16319 raw16319Labels permutation434 hz
    mixedMoment B raw16319step0 raw16319step0Labels = mixedMoment B raw16319step1 raw16319step1Labels := by
      have hz : ∀ j, raw16319step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16319step1 = (fun i j => raw16319step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16319step1 raw16319step0; decide +kernel
      have hl : raw16319step1Labels = raw16319step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16319step0 raw16319step0Labels permutation80 hz
    mixedMoment B raw16319step1 raw16319step1Labels = mixedMoment B raw16319step2 raw16319step2Labels := by
      have ha : raw16319step2 = (fun i j => raw16319step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16319step2 raw16319step1; decide +kernel
      have hl : raw16319step2Labels = raw16319step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16319step1 raw16319step1Labels permutation31 permutation3
    mixedMoment B raw16319step2 raw16319step2Labels = mixedMoment B raw16319step3 raw16319step3Labels := by
      have ha : raw16319step3 = -raw16319step2 := by apply Matrix.ext; change ∀ i j, raw16319step3 i j = -(raw16319step2 i j); unfold raw16319step3 raw16319step2; decide +kernel
      have hl : raw16319step3Labels = raw16319step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2604 node2604Labels := by rfl

def raw16320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16320Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16320step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16320step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16320step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16320 raw16320Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw16320 raw16320Labels = mixedMoment B raw16320step0 raw16320step0Labels := by
      have hz : ∀ j, raw16320 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16320step0 = (fun i j => raw16320 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16320step0 raw16320; decide +kernel
      have hl : raw16320step0Labels = raw16320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16320 raw16320Labels permutation434 hz
    mixedMoment B raw16320step0 raw16320step0Labels = mixedMoment B raw16320step1 raw16320step1Labels := by
      have ha : raw16320step1 = (fun i j => raw16320step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16320step1 raw16320step0; decide +kernel
      have hl : raw16320step1Labels = raw16320step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16320step0 raw16320step0Labels permutation149 permutation3
    mixedMoment B raw16320step1 raw16320step1Labels = mixedMoment B raw16320step2 raw16320step2Labels := by
      have ha : raw16320step2 = -raw16320step1 := by apply Matrix.ext; change ∀ i j, raw16320step2 i j = -(raw16320step1 i j); unfold raw16320step2 raw16320step1; decide +kernel
      have hl : raw16320step2Labels = raw16320step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2590 node2590Labels := by rfl

def raw16321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16321Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw16321step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16321step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16321step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16321step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw16321step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16321 raw16321Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw16321 raw16321Labels = mixedMoment B raw16321step0 raw16321step0Labels := by
      have hz : ∀ j, raw16321 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16321step0 = (fun i j => raw16321 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16321step0 raw16321; decide +kernel
      have hl : raw16321step0Labels = raw16321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16321 raw16321Labels permutation346 hz
    mixedMoment B raw16321step0 raw16321step0Labels = mixedMoment B raw16321step1 raw16321step1Labels := by
      have ha : raw16321step1 = (fun i j => raw16321step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16321step1 raw16321step0; decide +kernel
      have hl : raw16321step1Labels = raw16321step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16321step0 raw16321step0Labels permutation149 permutation3
    mixedMoment B raw16321step1 raw16321step1Labels = mixedMoment B raw16321step2 raw16321step2Labels := by
      have ha : raw16321step2 = -raw16321step1 := by apply Matrix.ext; change ∀ i j, raw16321step2 i j = -(raw16321step1 i j); unfold raw16321step2 raw16321step1; decide +kernel
      have hl : raw16321step2Labels = raw16321step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2590 node2590Labels := by rfl

def raw16322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw16322Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![3, -2, -1]]
def raw16322step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw16322step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16322step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw16322step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16322step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16322step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16322 raw16322Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw16322 raw16322Labels = mixedMoment B raw16322step0 raw16322step0Labels := by
      have hz : ∀ j, raw16322 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16322step0 = (fun i j => raw16322 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16322step0 raw16322; decide +kernel
      have hl : raw16322step0Labels = raw16322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16322 raw16322Labels permutation434 hz
    mixedMoment B raw16322step0 raw16322step0Labels = mixedMoment B raw16322step1 raw16322step1Labels := by
      have hz : ∀ j, raw16322step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16322step1 = (fun i j => raw16322step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16322step1 raw16322step0; decide +kernel
      have hl : raw16322step1Labels = raw16322step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16322step0 raw16322step0Labels permutation80 hz
    mixedMoment B raw16322step1 raw16322step1Labels = mixedMoment B raw16322step2 raw16322step2Labels := by
      have ha : raw16322step2 = (fun i j => raw16322step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16322step2 raw16322step1; decide +kernel
      have hl : raw16322step2Labels = raw16322step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16322step1 raw16322step1Labels permutation31 permutation3
    mixedMoment B raw16322step2 raw16322step2Labels = mixedMoment B raw16322step3 raw16322step3Labels := by
      have ha : raw16322step3 = -raw16322step2 := by apply Matrix.ext; change ∀ i j, raw16322step3 i j = -(raw16322step2 i j); unfold raw16322step3 raw16322step2; decide +kernel
      have hl : raw16322step3Labels = raw16322step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw16323 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16323step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16323step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16323step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16323step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16323step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16323 raw16323Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw16323 raw16323Labels = mixedMoment B raw16323step0 raw16323step0Labels := by
      have hz : ∀ j, raw16323 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16323step0 = (fun i j => raw16323 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16323step0 raw16323; decide +kernel
      have hl : raw16323step0Labels = raw16323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16323 raw16323Labels permutation346 hz
    mixedMoment B raw16323step0 raw16323step0Labels = mixedMoment B raw16323step1 raw16323step1Labels := by
      have ha : raw16323step1 = (fun i j => raw16323step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16323step1 raw16323step0; decide +kernel
      have hl : raw16323step1Labels = raw16323step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16323step0 raw16323step0Labels permutation32 permutation7
    mixedMoment B raw16323step1 raw16323step1Labels = mixedMoment B raw16323step2 raw16323step2Labels := by
      have ha : raw16323step2 = raw16323step1 := by apply Matrix.ext; unfold raw16323step2 raw16323step1; decide +kernel
      have hl : raw16323step1Labels = labelEmbedding10 ∘ raw16323step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16323step1 raw16323step1Labels raw16323step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw16324 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16324step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16324step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 1, 1], ![-1, -1, 2]]
def raw16324step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16324step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw16324step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16324 raw16324Labels = mixedMoment B node5475 node5475Labels := by
  calc
    mixedMoment B raw16324 raw16324Labels = mixedMoment B raw16324step0 raw16324step0Labels := by
      have hz : ∀ j, raw16324 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16324step0 = (fun i j => raw16324 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16324step0 raw16324; decide +kernel
      have hl : raw16324step0Labels = raw16324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16324 raw16324Labels permutation434 hz
    mixedMoment B raw16324step0 raw16324step0Labels = mixedMoment B raw16324step1 raw16324step1Labels := by
      have hz : ∀ j, raw16324step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16324step1 = (fun i j => raw16324step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16324step1 raw16324step0; decide +kernel
      have hl : raw16324step1Labels = raw16324step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16324step0 raw16324step0Labels permutation80 hz
    mixedMoment B raw16324step1 raw16324step1Labels = mixedMoment B raw16324step2 raw16324step2Labels := by
      have ha : raw16324step2 = (fun i j => raw16324step1 (permutation24 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16324step2 raw16324step1; decide +kernel
      have hl : raw16324step2Labels = raw16324step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16324step1 raw16324step1Labels permutation24 permutation2
    _ = mixedMoment B node5475 node5475Labels := by rfl

def raw16325 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16325step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16325step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16325step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16325step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16325step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16325 raw16325Labels = mixedMoment B node5413 node5413Labels := by
  calc
    mixedMoment B raw16325 raw16325Labels = mixedMoment B raw16325step0 raw16325step0Labels := by
      have hz : ∀ j, raw16325 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16325step0 = (fun i j => raw16325 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16325step0 raw16325; decide +kernel
      have hl : raw16325step0Labels = raw16325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16325 raw16325Labels permutation434 hz
    mixedMoment B raw16325step0 raw16325step0Labels = mixedMoment B raw16325step1 raw16325step1Labels := by
      have hz : ∀ j, raw16325step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16325step1 = (fun i j => raw16325step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16325step1 raw16325step0; decide +kernel
      have hl : raw16325step1Labels = raw16325step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16325step0 raw16325step0Labels permutation80 hz
    mixedMoment B raw16325step1 raw16325step1Labels = mixedMoment B raw16325step2 raw16325step2Labels := by
      have ha : raw16325step2 = (fun i j => raw16325step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16325step2 raw16325step1; decide +kernel
      have hl : raw16325step2Labels = raw16325step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16325step1 raw16325step1Labels permutation30 permutation2
    _ = mixedMoment B node5413 node5413Labels := by rfl

def raw16326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16326step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16326step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16326step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 3, -1]]
def raw16326step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16326step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw16326step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16326step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw16326step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16326 raw16326Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw16326 raw16326Labels = mixedMoment B raw16326step0 raw16326step0Labels := by
      have hz : ∀ j, raw16326 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16326step0 = (fun i j => raw16326 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16326step0 raw16326; decide +kernel
      have hl : raw16326step0Labels = raw16326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16326 raw16326Labels permutation434 hz
    mixedMoment B raw16326step0 raw16326step0Labels = mixedMoment B raw16326step1 raw16326step1Labels := by
      have hz : ∀ j, raw16326step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16326step1 = (fun i j => raw16326step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16326step1 raw16326step0; decide +kernel
      have hl : raw16326step1Labels = raw16326step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16326step0 raw16326step0Labels permutation80 hz
    mixedMoment B raw16326step1 raw16326step1Labels = mixedMoment B raw16326step2 raw16326step2Labels := by
      have ha : raw16326step2 = (fun i j => raw16326step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16326step2 raw16326step1; decide +kernel
      have hl : raw16326step2Labels = raw16326step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16326step1 raw16326step1Labels permutation11 permutation4
    mixedMoment B raw16326step2 raw16326step2Labels = mixedMoment B raw16326step3 raw16326step3Labels := by
      have ha : raw16326step3 = -raw16326step2 := by apply Matrix.ext; change ∀ i j, raw16326step3 i j = -(raw16326step2 i j); unfold raw16326step3 raw16326step2; decide +kernel
      have hl : raw16326step3Labels = raw16326step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16326step3 raw16326step3Labels = mixedMoment B raw16326step4 raw16326step4Labels := by
      have ha : raw16326step4 = raw16326step3 := by apply Matrix.ext; unfold raw16326step4 raw16326step3; decide +kernel
      have hl : raw16326step3Labels = labelEmbedding7 ∘ raw16326step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16326step3 raw16326step3Labels raw16326step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw16327 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16327step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw16327step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16327step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16327step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16327step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16327 raw16327Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw16327 raw16327Labels = mixedMoment B raw16327step0 raw16327step0Labels := by
      have hz : ∀ j, raw16327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16327step0 = (fun i j => raw16327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16327step0 raw16327; decide +kernel
      have hl : raw16327step0Labels = raw16327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16327 raw16327Labels permutation346 hz
    mixedMoment B raw16327step0 raw16327step0Labels = mixedMoment B raw16327step1 raw16327step1Labels := by
      have ha : raw16327step1 = (fun i j => raw16327step0 (permutation61 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16327step1 raw16327step0; decide +kernel
      have hl : raw16327step1Labels = raw16327step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16327step0 raw16327step0Labels permutation61 permutation3
    mixedMoment B raw16327step1 raw16327step1Labels = mixedMoment B raw16327step2 raw16327step2Labels := by
      have ha : raw16327step2 = -raw16327step1 := by apply Matrix.ext; change ∀ i j, raw16327step2 i j = -(raw16327step1 i j); unfold raw16327step2 raw16327step1; decide +kernel
      have hl : raw16327step2Labels = raw16327step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16327step2 raw16327step2Labels = mixedMoment B raw16327step3 raw16327step3Labels := by
      have ha : raw16327step3 = raw16327step2 := by apply Matrix.ext; unfold raw16327step3 raw16327step2; decide +kernel
      have hl : raw16327step2Labels = labelEmbedding6 ∘ raw16327step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16327step2 raw16327step2Labels raw16327step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw16328 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw16328step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16328step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-2, 1, 1], ![-1, -1, 2]]
def raw16328step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16328step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw16328step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16328step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16328step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16328step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw16328step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16328 raw16328Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw16328 raw16328Labels = mixedMoment B raw16328step0 raw16328step0Labels := by
      have hz : ∀ j, raw16328 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16328step0 = (fun i j => raw16328 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16328step0 raw16328; decide +kernel
      have hl : raw16328step0Labels = raw16328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16328 raw16328Labels permutation434 hz
    mixedMoment B raw16328step0 raw16328step0Labels = mixedMoment B raw16328step1 raw16328step1Labels := by
      have hz : ∀ j, raw16328step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16328step1 = (fun i j => raw16328step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16328step1 raw16328step0; decide +kernel
      have hl : raw16328step1Labels = raw16328step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16328step0 raw16328step0Labels permutation80 hz
    mixedMoment B raw16328step1 raw16328step1Labels = mixedMoment B raw16328step2 raw16328step2Labels := by
      have ha : raw16328step2 = (fun i j => raw16328step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16328step2 raw16328step1; decide +kernel
      have hl : raw16328step2Labels = raw16328step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16328step1 raw16328step1Labels permutation15 permutation3
    mixedMoment B raw16328step2 raw16328step2Labels = mixedMoment B raw16328step3 raw16328step3Labels := by
      have ha : raw16328step3 = -raw16328step2 := by apply Matrix.ext; change ∀ i j, raw16328step3 i j = -(raw16328step2 i j); unfold raw16328step3 raw16328step2; decide +kernel
      have hl : raw16328step3Labels = raw16328step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16328step3 raw16328step3Labels = mixedMoment B raw16328step4 raw16328step4Labels := by
      have ha : raw16328step4 = raw16328step3 := by apply Matrix.ext; unfold raw16328step4 raw16328step3; decide +kernel
      have hl : raw16328step3Labels = labelEmbedding6 ∘ raw16328step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16328step3 raw16328step3Labels raw16328step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw16329 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw16329step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw16329step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16329step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw16329step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16329step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16329step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16329step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw16329step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16329 raw16329Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw16329 raw16329Labels = mixedMoment B raw16329step0 raw16329step0Labels := by
      have hz : ∀ j, raw16329 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16329step0 = (fun i j => raw16329 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16329step0 raw16329; decide +kernel
      have hl : raw16329step0Labels = raw16329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16329 raw16329Labels permutation434 hz
    mixedMoment B raw16329step0 raw16329step0Labels = mixedMoment B raw16329step1 raw16329step1Labels := by
      have hz : ∀ j, raw16329step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16329step1 = (fun i j => raw16329step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16329step1 raw16329step0; decide +kernel
      have hl : raw16329step1Labels = raw16329step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16329step0 raw16329step0Labels permutation80 hz
    mixedMoment B raw16329step1 raw16329step1Labels = mixedMoment B raw16329step2 raw16329step2Labels := by
      have ha : raw16329step2 = (fun i j => raw16329step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16329step2 raw16329step1; decide +kernel
      have hl : raw16329step2Labels = raw16329step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16329step1 raw16329step1Labels permutation14 permutation3
    mixedMoment B raw16329step2 raw16329step2Labels = mixedMoment B raw16329step3 raw16329step3Labels := by
      have ha : raw16329step3 = -raw16329step2 := by apply Matrix.ext; change ∀ i j, raw16329step3 i j = -(raw16329step2 i j); unfold raw16329step3 raw16329step2; decide +kernel
      have hl : raw16329step3Labels = raw16329step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16329step3 raw16329step3Labels = mixedMoment B raw16329step4 raw16329step4Labels := by
      have ha : raw16329step4 = raw16329step3 := by apply Matrix.ext; unfold raw16329step4 raw16329step3; decide +kernel
      have hl : raw16329step3Labels = labelEmbedding6 ∘ raw16329step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16329step3 raw16329step3Labels raw16329step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw16330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16330step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16330step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16330step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16330step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16330step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16330 raw16330Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw16330 raw16330Labels = mixedMoment B raw16330step0 raw16330step0Labels := by
      have hz : ∀ j, raw16330 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16330step0 = (fun i j => raw16330 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16330step0 raw16330; decide +kernel
      have hl : raw16330step0Labels = raw16330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16330 raw16330Labels permutation434 hz
    mixedMoment B raw16330step0 raw16330step0Labels = mixedMoment B raw16330step1 raw16330step1Labels := by
      have ha : raw16330step1 = (fun i j => raw16330step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16330step1 raw16330step0; decide +kernel
      have hl : raw16330step1Labels = raw16330step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16330step0 raw16330step0Labels permutation44 permutation4
    mixedMoment B raw16330step1 raw16330step1Labels = mixedMoment B raw16330step2 raw16330step2Labels := by
      have ha : raw16330step2 = -raw16330step1 := by apply Matrix.ext; change ∀ i j, raw16330step2 i j = -(raw16330step1 i j); unfold raw16330step2 raw16330step1; decide +kernel
      have hl : raw16330step2Labels = raw16330step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16330step2 raw16330step2Labels = mixedMoment B raw16330step3 raw16330step3Labels := by
      have ha : raw16330step3 = raw16330step2 := by apply Matrix.ext; unfold raw16330step3 raw16330step2; decide +kernel
      have hl : raw16330step2Labels = labelEmbedding7 ∘ raw16330step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16330step2 raw16330step2Labels raw16330step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw16331 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16331step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16331step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16331step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16331step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16331step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16331 raw16331Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw16331 raw16331Labels = mixedMoment B raw16331step0 raw16331step0Labels := by
      have ha : raw16331step0 = (fun i j => raw16331 (permutation212 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16331step0 raw16331; decide +kernel
      have hl : raw16331step0Labels = raw16331Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16331 raw16331Labels permutation212 permutation4
    mixedMoment B raw16331step0 raw16331step0Labels = mixedMoment B raw16331step1 raw16331step1Labels := by
      have ha : raw16331step1 = -raw16331step0 := by apply Matrix.ext; change ∀ i j, raw16331step1 i j = -(raw16331step0 i j); unfold raw16331step1 raw16331step0; decide +kernel
      have hl : raw16331step1Labels = raw16331step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16331step1 raw16331step1Labels = mixedMoment B raw16331step2 raw16331step2Labels := by
      have ha : raw16331step2 = raw16331step1 := by apply Matrix.ext; unfold raw16331step2 raw16331step1; decide +kernel
      have hl : raw16331step1Labels = labelEmbedding7 ∘ raw16331step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16331step1 raw16331step1Labels raw16331step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw16332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16332step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, -1, 1], ![-1, -1, 2]]
def raw16332step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16332step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16332step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16332step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16332step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16332step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16332step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16332 raw16332Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw16332 raw16332Labels = mixedMoment B raw16332step0 raw16332step0Labels := by
      have hz : ∀ j, raw16332 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16332step0 = (fun i j => raw16332 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16332step0 raw16332; decide +kernel
      have hl : raw16332step0Labels = raw16332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16332 raw16332Labels permutation434 hz
    mixedMoment B raw16332step0 raw16332step0Labels = mixedMoment B raw16332step1 raw16332step1Labels := by
      have hz : ∀ j, raw16332step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16332step1 = (fun i j => raw16332step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16332step1 raw16332step0; decide +kernel
      have hl : raw16332step1Labels = raw16332step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16332step0 raw16332step0Labels permutation80 hz
    mixedMoment B raw16332step1 raw16332step1Labels = mixedMoment B raw16332step2 raw16332step2Labels := by
      have ha : raw16332step2 = (fun i j => raw16332step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16332step2 raw16332step1; decide +kernel
      have hl : raw16332step2Labels = raw16332step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16332step1 raw16332step1Labels permutation8 permutation4
    mixedMoment B raw16332step2 raw16332step2Labels = mixedMoment B raw16332step3 raw16332step3Labels := by
      have ha : raw16332step3 = -raw16332step2 := by apply Matrix.ext; change ∀ i j, raw16332step3 i j = -(raw16332step2 i j); unfold raw16332step3 raw16332step2; decide +kernel
      have hl : raw16332step3Labels = raw16332step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16332step3 raw16332step3Labels = mixedMoment B raw16332step4 raw16332step4Labels := by
      have ha : raw16332step4 = raw16332step3 := by apply Matrix.ext; unfold raw16332step4 raw16332step3; decide +kernel
      have hl : raw16332step3Labels = labelEmbedding7 ∘ raw16332step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16332step3 raw16332step3Labels raw16332step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw16333 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw16333step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16333step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16333step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16333step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16333step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16333step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16333 raw16333Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw16333 raw16333Labels = mixedMoment B raw16333step0 raw16333step0Labels := by
      have hz : ∀ j, raw16333 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16333step0 = (fun i j => raw16333 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16333step0 raw16333; decide +kernel
      have hl : raw16333step0Labels = raw16333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16333 raw16333Labels permutation346 hz
    mixedMoment B raw16333step0 raw16333step0Labels = mixedMoment B raw16333step1 raw16333step1Labels := by
      have ha : raw16333step1 = (fun i j => raw16333step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16333step1 raw16333step0; decide +kernel
      have hl : raw16333step1Labels = raw16333step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16333step0 raw16333step0Labels permutation38 permutation4
    mixedMoment B raw16333step1 raw16333step1Labels = mixedMoment B raw16333step2 raw16333step2Labels := by
      have ha : raw16333step2 = -raw16333step1 := by apply Matrix.ext; change ∀ i j, raw16333step2 i j = -(raw16333step1 i j); unfold raw16333step2 raw16333step1; decide +kernel
      have hl : raw16333step2Labels = raw16333step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16333step2 raw16333step2Labels = mixedMoment B raw16333step3 raw16333step3Labels := by
      have ha : raw16333step3 = raw16333step2 := by apply Matrix.ext; unfold raw16333step3 raw16333step2; decide +kernel
      have hl : raw16333step2Labels = labelEmbedding7 ∘ raw16333step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16333step2 raw16333step2Labels raw16333step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw16334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16334step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 0, 1], ![0, -2, 2]]
def raw16334step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16334step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw16334step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16334step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16334step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16334step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16334step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16334 raw16334Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw16334 raw16334Labels = mixedMoment B raw16334step0 raw16334step0Labels := by
      have hz : ∀ j, raw16334 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16334step0 = (fun i j => raw16334 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16334step0 raw16334; decide +kernel
      have hl : raw16334step0Labels = raw16334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16334 raw16334Labels permutation434 hz
    mixedMoment B raw16334step0 raw16334step0Labels = mixedMoment B raw16334step1 raw16334step1Labels := by
      have hz : ∀ j, raw16334step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16334step1 = (fun i j => raw16334step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16334step1 raw16334step0; decide +kernel
      have hl : raw16334step1Labels = raw16334step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16334step0 raw16334step0Labels permutation80 hz
    mixedMoment B raw16334step1 raw16334step1Labels = mixedMoment B raw16334step2 raw16334step2Labels := by
      have ha : raw16334step2 = (fun i j => raw16334step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16334step2 raw16334step1; decide +kernel
      have hl : raw16334step2Labels = raw16334step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16334step1 raw16334step1Labels permutation10 permutation4
    mixedMoment B raw16334step2 raw16334step2Labels = mixedMoment B raw16334step3 raw16334step3Labels := by
      have ha : raw16334step3 = -raw16334step2 := by apply Matrix.ext; change ∀ i j, raw16334step3 i j = -(raw16334step2 i j); unfold raw16334step3 raw16334step2; decide +kernel
      have hl : raw16334step3Labels = raw16334step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16334step3 raw16334step3Labels = mixedMoment B raw16334step4 raw16334step4Labels := by
      have ha : raw16334step4 = raw16334step3 := by apply Matrix.ext; unfold raw16334step4 raw16334step3; decide +kernel
      have hl : raw16334step3Labels = labelEmbedding7 ∘ raw16334step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16334step3 raw16334step3Labels raw16334step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw16335 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw16335step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw16335step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16335step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16335step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16335step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16335step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16335 raw16335Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw16335 raw16335Labels = mixedMoment B raw16335step0 raw16335step0Labels := by
      have hz : ∀ j, raw16335 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16335step0 = (fun i j => raw16335 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16335step0 raw16335; decide +kernel
      have hl : raw16335step0Labels = raw16335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16335 raw16335Labels permutation346 hz
    mixedMoment B raw16335step0 raw16335step0Labels = mixedMoment B raw16335step1 raw16335step1Labels := by
      have ha : raw16335step1 = (fun i j => raw16335step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16335step1 raw16335step0; decide +kernel
      have hl : raw16335step1Labels = raw16335step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16335step0 raw16335step0Labels permutation40 permutation4
    mixedMoment B raw16335step1 raw16335step1Labels = mixedMoment B raw16335step2 raw16335step2Labels := by
      have ha : raw16335step2 = -raw16335step1 := by apply Matrix.ext; change ∀ i j, raw16335step2 i j = -(raw16335step1 i j); unfold raw16335step2 raw16335step1; decide +kernel
      have hl : raw16335step2Labels = raw16335step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16335step2 raw16335step2Labels = mixedMoment B raw16335step3 raw16335step3Labels := by
      have ha : raw16335step3 = raw16335step2 := by apply Matrix.ext; unfold raw16335step3 raw16335step2; decide +kernel
      have hl : raw16335step2Labels = labelEmbedding7 ∘ raw16335step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16335step2 raw16335step2Labels raw16335step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw16336 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16336Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw16336step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 1, 1], ![0, -2, 2]]
def raw16336step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16336step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16336step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16336step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw16336step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16336 raw16336Labels = mixedMoment B node5449 node5449Labels := by
  calc
    mixedMoment B raw16336 raw16336Labels = mixedMoment B raw16336step0 raw16336step0Labels := by
      have hz : ∀ j, raw16336 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw16336step0 = (fun i j => raw16336 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw16336step0 raw16336; decide +kernel
      have hl : raw16336step0Labels = raw16336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16336 raw16336Labels permutation434 hz
    mixedMoment B raw16336step0 raw16336step0Labels = mixedMoment B raw16336step1 raw16336step1Labels := by
      have hz : ∀ j, raw16336step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw16336step1 = (fun i j => raw16336step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw16336step1 raw16336step0; decide +kernel
      have hl : raw16336step1Labels = raw16336step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16336step0 raw16336step0Labels permutation80 hz
    mixedMoment B raw16336step1 raw16336step1Labels = mixedMoment B raw16336step2 raw16336step2Labels := by
      have ha : raw16336step2 = (fun i j => raw16336step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16336step2 raw16336step1; decide +kernel
      have hl : raw16336step2Labels = raw16336step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16336step1 raw16336step1Labels permutation29 permutation4
    mixedMoment B raw16336step2 raw16336step2Labels = mixedMoment B raw16336step3 raw16336step3Labels := by
      have ha : raw16336step3 = raw16336step2 := by apply Matrix.ext; unfold raw16336step3 raw16336step2; decide +kernel
      have hl : raw16336step2Labels = labelEmbedding7 ∘ raw16336step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16336step2 raw16336step2Labels raw16336step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5449 node5449Labels := by rfl

def raw16337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16337step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16337step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16337step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16337step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16337step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16337step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16337step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16337 raw16337Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw16337 raw16337Labels = mixedMoment B raw16337step0 raw16337step0Labels := by
      have hz : ∀ j, raw16337 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16337step0 = (fun i j => raw16337 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16337step0 raw16337; decide +kernel
      have hl : raw16337step0Labels = raw16337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16337 raw16337Labels permutation346 hz
    mixedMoment B raw16337step0 raw16337step0Labels = mixedMoment B raw16337step1 raw16337step1Labels := by
      have ha : raw16337step1 = (fun i j => raw16337step0 (permutation63 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16337step1 raw16337step0; decide +kernel
      have hl : raw16337step1Labels = raw16337step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16337step0 raw16337step0Labels permutation63 permutation5
    mixedMoment B raw16337step1 raw16337step1Labels = mixedMoment B raw16337step2 raw16337step2Labels := by
      have ha : raw16337step2 = -raw16337step1 := by apply Matrix.ext; change ∀ i j, raw16337step2 i j = -(raw16337step1 i j); unfold raw16337step2 raw16337step1; decide +kernel
      have hl : raw16337step2Labels = raw16337step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16337step2 raw16337step2Labels = mixedMoment B raw16337step3 raw16337step3Labels := by
      have ha : raw16337step3 = raw16337step2 := by apply Matrix.ext; unfold raw16337step3 raw16337step2; decide +kernel
      have hl : raw16337step2Labels = labelEmbedding8 ∘ raw16337step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16337step2 raw16337step2Labels raw16337step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5164 node5164Labels := by rfl

def raw16338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16338step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16338step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16338 raw16338Labels = mixedMoment B node5470 node5470Labels := by
  calc
    mixedMoment B raw16338 raw16338Labels = mixedMoment B raw16338step0 raw16338step0Labels := by
      have ha : raw16338step0 = (fun i j => raw16338 (permutation528 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16338step0 raw16338; decide +kernel
      have hl : raw16338step0Labels = raw16338Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16338 raw16338Labels permutation528 permutation4
    mixedMoment B raw16338step0 raw16338step0Labels = mixedMoment B raw16338step1 raw16338step1Labels := by
      have ha : raw16338step1 = raw16338step0 := by apply Matrix.ext; unfold raw16338step1 raw16338step0; decide +kernel
      have hl : raw16338step0Labels = labelEmbedding7 ∘ raw16338step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16338step0 raw16338step0Labels raw16338step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5470 node5470Labels := by rfl

def raw16339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16339step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16339step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16339step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16339step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16339step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16339step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16339 raw16339Labels = mixedMoment B node5463 node5463Labels := by
  calc
    mixedMoment B raw16339 raw16339Labels = mixedMoment B raw16339step0 raw16339step0Labels := by
      have hz : ∀ j, raw16339 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16339step0 = (fun i j => raw16339 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16339step0 raw16339; decide +kernel
      have hl : raw16339step0Labels = raw16339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16339 raw16339Labels permutation346 hz
    mixedMoment B raw16339step0 raw16339step0Labels = mixedMoment B raw16339step1 raw16339step1Labels := by
      have ha : raw16339step1 = (fun i j => raw16339step0 (permutation66 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16339step1 raw16339step0; decide +kernel
      have hl : raw16339step1Labels = raw16339step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16339step0 raw16339step0Labels permutation66 permutation4
    mixedMoment B raw16339step1 raw16339step1Labels = mixedMoment B raw16339step2 raw16339step2Labels := by
      have ha : raw16339step2 = -raw16339step1 := by apply Matrix.ext; change ∀ i j, raw16339step2 i j = -(raw16339step1 i j); unfold raw16339step2 raw16339step1; decide +kernel
      have hl : raw16339step2Labels = raw16339step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16339step2 raw16339step2Labels = mixedMoment B raw16339step3 raw16339step3Labels := by
      have ha : raw16339step3 = raw16339step2 := by apply Matrix.ext; unfold raw16339step3 raw16339step2; decide +kernel
      have hl : raw16339step2Labels = labelEmbedding7 ∘ raw16339step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16339step2 raw16339step2Labels raw16339step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5463 node5463Labels := by rfl

def raw16340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16340step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16340step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16340step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16340step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16340step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16340step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16340 raw16340Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw16340 raw16340Labels = mixedMoment B raw16340step0 raw16340step0Labels := by
      have hz : ∀ j, raw16340 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16340step0 = (fun i j => raw16340 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16340step0 raw16340; decide +kernel
      have hl : raw16340step0Labels = raw16340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16340 raw16340Labels permutation346 hz
    mixedMoment B raw16340step0 raw16340step0Labels = mixedMoment B raw16340step1 raw16340step1Labels := by
      have ha : raw16340step1 = (fun i j => raw16340step0 (permutation67 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16340step1 raw16340step0; decide +kernel
      have hl : raw16340step1Labels = raw16340step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16340step0 raw16340step0Labels permutation67 permutation4
    mixedMoment B raw16340step1 raw16340step1Labels = mixedMoment B raw16340step2 raw16340step2Labels := by
      have ha : raw16340step2 = -raw16340step1 := by apply Matrix.ext; change ∀ i j, raw16340step2 i j = -(raw16340step1 i j); unfold raw16340step2 raw16340step1; decide +kernel
      have hl : raw16340step2Labels = raw16340step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16340step2 raw16340step2Labels = mixedMoment B raw16340step3 raw16340step3Labels := by
      have ha : raw16340step3 = raw16340step2 := by apply Matrix.ext; unfold raw16340step3 raw16340step2; decide +kernel
      have hl : raw16340step2Labels = labelEmbedding7 ∘ raw16340step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16340step2 raw16340step2Labels raw16340step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw16341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16341step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16341step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw16341step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw16341step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16341 raw16341Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw16341 raw16341Labels = mixedMoment B raw16341step0 raw16341step0Labels := by
      have hz : ∀ j, raw16341 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16341step0 = (fun i j => raw16341 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16341step0 raw16341; decide +kernel
      have hl : raw16341step0Labels = raw16341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16341 raw16341Labels permutation346 hz
    mixedMoment B raw16341step0 raw16341step0Labels = mixedMoment B raw16341step1 raw16341step1Labels := by
      have ha : raw16341step1 = (fun i j => raw16341step0 (permutation109 i) (permutation4 j)) := by apply Matrix.ext; unfold raw16341step1 raw16341step0; decide +kernel
      have hl : raw16341step1Labels = raw16341step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16341step0 raw16341step0Labels permutation109 permutation4
    mixedMoment B raw16341step1 raw16341step1Labels = mixedMoment B raw16341step2 raw16341step2Labels := by
      have ha : raw16341step2 = raw16341step1 := by apply Matrix.ext; unfold raw16341step2 raw16341step1; decide +kernel
      have hl : raw16341step1Labels = labelEmbedding7 ∘ raw16341step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16341step1 raw16341step1Labels raw16341step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw16342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16342step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16342 raw16342Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw16342 raw16342Labels = mixedMoment B raw16342step0 raw16342step0Labels := by
      have hz : ∀ j, raw16342 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16342step0 = (fun i j => raw16342 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16342step0 raw16342; decide +kernel
      have hl : raw16342step0Labels = raw16342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16342 raw16342Labels permutation346 hz
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw16343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16343step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16343 raw16343Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw16343 raw16343Labels = mixedMoment B raw16343step0 raw16343step0Labels := by
      have ha : raw16343step0 = (fun i j => raw16343 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16343step0 raw16343; decide +kernel
      have hl : raw16343step0Labels = raw16343Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16343 raw16343Labels permutation176 permutation2
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw16344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16344step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16344step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16344 raw16344Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw16344 raw16344Labels = mixedMoment B raw16344step0 raw16344step0Labels := by
      have hz : ∀ j, raw16344 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16344step0 = (fun i j => raw16344 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16344step0 raw16344; decide +kernel
      have hl : raw16344step0Labels = raw16344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16344 raw16344Labels permutation346 hz
    mixedMoment B raw16344step0 raw16344step0Labels = mixedMoment B raw16344step1 raw16344step1Labels := by
      have ha : raw16344step1 = (fun i j => raw16344step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16344step1 raw16344step0; decide +kernel
      have hl : raw16344step1Labels = raw16344step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16344step0 raw16344step0Labels permutation38 permutation2
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw16345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw16345step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16345step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16345step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16345step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw16345step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16345 raw16345Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw16345 raw16345Labels = mixedMoment B raw16345step0 raw16345step0Labels := by
      have hz : ∀ j, raw16345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16345step0 = (fun i j => raw16345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16345step0 raw16345; decide +kernel
      have hl : raw16345step0Labels = raw16345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16345 raw16345Labels permutation346 hz
    mixedMoment B raw16345step0 raw16345step0Labels = mixedMoment B raw16345step1 raw16345step1Labels := by
      have ha : raw16345step1 = (fun i j => raw16345step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16345step1 raw16345step0; decide +kernel
      have hl : raw16345step1Labels = raw16345step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16345step0 raw16345step0Labels permutation44 permutation7
    mixedMoment B raw16345step1 raw16345step1Labels = mixedMoment B raw16345step2 raw16345step2Labels := by
      have ha : raw16345step2 = -raw16345step1 := by apply Matrix.ext; change ∀ i j, raw16345step2 i j = -(raw16345step1 i j); unfold raw16345step2 raw16345step1; decide +kernel
      have hl : raw16345step2Labels = raw16345step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16345step2 raw16345step2Labels = mixedMoment B raw16345step3 raw16345step3Labels := by
      have ha : raw16345step3 = raw16345step2 := by apply Matrix.ext; unfold raw16345step3 raw16345step2; decide +kernel
      have hl : raw16345step2Labels = labelEmbedding10 ∘ raw16345step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16345step2 raw16345step2Labels raw16345step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw16346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16346step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw16346step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16346step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16346step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16346step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw16346step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16346 raw16346Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw16346 raw16346Labels = mixedMoment B raw16346step0 raw16346step0Labels := by
      have hz : ∀ j, raw16346 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16346step0 = (fun i j => raw16346 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16346step0 raw16346; decide +kernel
      have hl : raw16346step0Labels = raw16346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16346 raw16346Labels permutation346 hz
    mixedMoment B raw16346step0 raw16346step0Labels = mixedMoment B raw16346step1 raw16346step1Labels := by
      have ha : raw16346step1 = (fun i j => raw16346step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16346step1 raw16346step0; decide +kernel
      have hl : raw16346step1Labels = raw16346step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16346step0 raw16346step0Labels permutation44 permutation7
    mixedMoment B raw16346step1 raw16346step1Labels = mixedMoment B raw16346step2 raw16346step2Labels := by
      have ha : raw16346step2 = -raw16346step1 := by apply Matrix.ext; change ∀ i j, raw16346step2 i j = -(raw16346step1 i j); unfold raw16346step2 raw16346step1; decide +kernel
      have hl : raw16346step2Labels = raw16346step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16346step2 raw16346step2Labels = mixedMoment B raw16346step3 raw16346step3Labels := by
      have ha : raw16346step3 = raw16346step2 := by apply Matrix.ext; unfold raw16346step3 raw16346step2; decide +kernel
      have hl : raw16346step2Labels = labelEmbedding10 ∘ raw16346step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16346step2 raw16346step2Labels raw16346step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw16347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw16347step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16347 raw16347Labels = mixedMoment B node5190 node5190Labels := by
  calc
    mixedMoment B raw16347 raw16347Labels = mixedMoment B raw16347step0 raw16347step0Labels := by
      have ha : raw16347step0 = (fun i j => raw16347 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16347step0 raw16347; decide +kernel
      have hl : raw16347step0Labels = raw16347Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16347 raw16347Labels permutation160 permutation2
    _ = mixedMoment B node5190 node5190Labels := by rfl

def raw16348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16348step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16348step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16348step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16348step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16348step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16348 raw16348Labels = mixedMoment B node5124 node5124Labels := by
  calc
    mixedMoment B raw16348 raw16348Labels = mixedMoment B raw16348step0 raw16348step0Labels := by
      have ha : raw16348step0 = (fun i j => raw16348 (permutation306 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16348step0 raw16348; decide +kernel
      have hl : raw16348step0Labels = raw16348Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16348 raw16348Labels permutation306 permutation5
    mixedMoment B raw16348step0 raw16348step0Labels = mixedMoment B raw16348step1 raw16348step1Labels := by
      have ha : raw16348step1 = -raw16348step0 := by apply Matrix.ext; change ∀ i j, raw16348step1 i j = -(raw16348step0 i j); unfold raw16348step1 raw16348step0; decide +kernel
      have hl : raw16348step1Labels = raw16348step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16348step1 raw16348step1Labels = mixedMoment B raw16348step2 raw16348step2Labels := by
      have ha : raw16348step2 = raw16348step1 := by apply Matrix.ext; unfold raw16348step2 raw16348step1; decide +kernel
      have hl : raw16348step1Labels = labelEmbedding8 ∘ raw16348step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16348step1 raw16348step1Labels raw16348step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5124 node5124Labels := by rfl

def raw16349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16349step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw16349step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16349 raw16349Labels = mixedMoment B node5444 node5444Labels := by
  calc
    mixedMoment B raw16349 raw16349Labels = mixedMoment B raw16349step0 raw16349step0Labels := by
      have ha : raw16349step0 = (fun i j => raw16349 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16349step0 raw16349; decide +kernel
      have hl : raw16349step0Labels = raw16349Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16349 raw16349Labels permutation160 permutation2
    _ = mixedMoment B node5444 node5444Labels := by rfl

def raw16350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16350step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw16350step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16350step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16350step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16350step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw16350step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16350 raw16350Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw16350 raw16350Labels = mixedMoment B raw16350step0 raw16350step0Labels := by
      have ha : raw16350step0 = (fun i j => raw16350 (permutation230 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16350step0 raw16350; decide +kernel
      have hl : raw16350step0Labels = raw16350Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16350 raw16350Labels permutation230 permutation7
    mixedMoment B raw16350step0 raw16350step0Labels = mixedMoment B raw16350step1 raw16350step1Labels := by
      have ha : raw16350step1 = -raw16350step0 := by apply Matrix.ext; change ∀ i j, raw16350step1 i j = -(raw16350step0 i j); unfold raw16350step1 raw16350step0; decide +kernel
      have hl : raw16350step1Labels = raw16350step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16350step1 raw16350step1Labels = mixedMoment B raw16350step2 raw16350step2Labels := by
      have ha : raw16350step2 = raw16350step1 := by apply Matrix.ext; unfold raw16350step2 raw16350step1; decide +kernel
      have hl : raw16350step1Labels = labelEmbedding10 ∘ raw16350step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16350step1 raw16350step1Labels raw16350step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw16351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw16351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16351 raw16351Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw16351 raw16351Labels = mixedMoment B raw16351step0 raw16351step0Labels := by
      have ha : raw16351step0 = (fun i j => raw16351 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16351step0 raw16351; decide +kernel
      have hl : raw16351step0Labels = raw16351Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16351 raw16351Labels permutation160 permutation2
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw16352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16352step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16352 raw16352Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw16352 raw16352Labels = mixedMoment B raw16352step0 raw16352step0Labels := by
      have hz : ∀ j, raw16352 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16352step0 = (fun i j => raw16352 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16352step0 raw16352; decide +kernel
      have hl : raw16352step0Labels = raw16352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16352 raw16352Labels permutation346 hz
    mixedMoment B raw16352step0 raw16352step0Labels = mixedMoment B raw16352step1 raw16352step1Labels := by
      have ha : raw16352step1 = (fun i j => raw16352step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16352step1 raw16352step0; decide +kernel
      have hl : raw16352step1Labels = raw16352step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16352step0 raw16352step0Labels permutation34 permutation2
    _ = mixedMoment B node5199 node5199Labels := by rfl

def raw16353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw16353step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16353step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16353step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16353step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16353step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16353 raw16353Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw16353 raw16353Labels = mixedMoment B raw16353step0 raw16353step0Labels := by
      have hz : ∀ j, raw16353 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16353step0 = (fun i j => raw16353 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16353step0 raw16353; decide +kernel
      have hl : raw16353step0Labels = raw16353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16353 raw16353Labels permutation346 hz
    mixedMoment B raw16353step0 raw16353step0Labels = mixedMoment B raw16353step1 raw16353step1Labels := by
      have ha : raw16353step1 = (fun i j => raw16353step0 (permutation57 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16353step1 raw16353step0; decide +kernel
      have hl : raw16353step1Labels = raw16353step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16353step0 raw16353step0Labels permutation57 permutation5
    mixedMoment B raw16353step1 raw16353step1Labels = mixedMoment B raw16353step2 raw16353step2Labels := by
      have ha : raw16353step2 = -raw16353step1 := by apply Matrix.ext; change ∀ i j, raw16353step2 i j = -(raw16353step1 i j); unfold raw16353step2 raw16353step1; decide +kernel
      have hl : raw16353step2Labels = raw16353step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16353step2 raw16353step2Labels = mixedMoment B raw16353step3 raw16353step3Labels := by
      have ha : raw16353step3 = raw16353step2 := by apply Matrix.ext; unfold raw16353step3 raw16353step2; decide +kernel
      have hl : raw16353step2Labels = labelEmbedding8 ∘ raw16353step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16353step2 raw16353step2Labels raw16353step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5229 node5229Labels := by rfl

def raw16354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw16354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16354 raw16354Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw16354 raw16354Labels = mixedMoment B raw16354step0 raw16354step0Labels := by
      have ha : raw16354step0 = (fun i j => raw16354 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16354step0 raw16354; decide +kernel
      have hl : raw16354step0Labels = raw16354Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16354 raw16354Labels permutation178 permutation2
    _ = mixedMoment B node5421 node5421Labels := by rfl

def raw16355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16355step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16355step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16355step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw16355step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16355step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16355 raw16355Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw16355 raw16355Labels = mixedMoment B raw16355step0 raw16355step0Labels := by
      have hz : ∀ j, raw16355 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16355step0 = (fun i j => raw16355 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16355step0 raw16355; decide +kernel
      have hl : raw16355step0Labels = raw16355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16355 raw16355Labels permutation346 hz
    mixedMoment B raw16355step0 raw16355step0Labels = mixedMoment B raw16355step1 raw16355step1Labels := by
      have ha : raw16355step1 = (fun i j => raw16355step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw16355step1 raw16355step0; decide +kernel
      have hl : raw16355step1Labels = raw16355step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16355step0 raw16355step0Labels permutation44 permutation7
    mixedMoment B raw16355step1 raw16355step1Labels = mixedMoment B raw16355step2 raw16355step2Labels := by
      have ha : raw16355step2 = -raw16355step1 := by apply Matrix.ext; change ∀ i j, raw16355step2 i j = -(raw16355step1 i j); unfold raw16355step2 raw16355step1; decide +kernel
      have hl : raw16355step2Labels = raw16355step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16355step2 raw16355step2Labels = mixedMoment B raw16355step3 raw16355step3Labels := by
      have ha : raw16355step3 = raw16355step2 := by apply Matrix.ext; unfold raw16355step3 raw16355step2; decide +kernel
      have hl : raw16355step2Labels = labelEmbedding10 ∘ raw16355step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16355step2 raw16355step2Labels raw16355step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw16356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16356step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw16356step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16356 raw16356Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw16356 raw16356Labels = mixedMoment B raw16356step0 raw16356step0Labels := by
      have hz : ∀ j, raw16356 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16356step0 = (fun i j => raw16356 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16356step0 raw16356; decide +kernel
      have hl : raw16356step0Labels = raw16356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16356 raw16356Labels permutation346 hz
    mixedMoment B raw16356step0 raw16356step0Labels = mixedMoment B raw16356step1 raw16356step1Labels := by
      have ha : raw16356step1 = (fun i j => raw16356step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw16356step1 raw16356step0; decide +kernel
      have hl : raw16356step1Labels = raw16356step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16356step0 raw16356step0Labels permutation34 permutation2
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw16357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16357step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw16357step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16357step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw16357step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16357 raw16357Labels = mixedMoment B node5016 node5016Labels := by
  calc
    mixedMoment B raw16357 raw16357Labels = mixedMoment B raw16357step0 raw16357step0Labels := by
      have hz : ∀ j, raw16357 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16357step0 = (fun i j => raw16357 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16357step0 raw16357; decide +kernel
      have hl : raw16357step0Labels = raw16357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16357 raw16357Labels permutation346 hz
    mixedMoment B raw16357step0 raw16357step0Labels = mixedMoment B raw16357step1 raw16357step1Labels := by
      have ha : raw16357step1 = (fun i j => raw16357step0 (permutation126 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16357step1 raw16357step0; decide +kernel
      have hl : raw16357step1Labels = raw16357step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16357step0 raw16357step0Labels permutation126 permutation5
    mixedMoment B raw16357step1 raw16357step1Labels = mixedMoment B raw16357step2 raw16357step2Labels := by
      have ha : raw16357step2 = raw16357step1 := by apply Matrix.ext; unfold raw16357step2 raw16357step1; decide +kernel
      have hl : raw16357step1Labels = labelEmbedding8 ∘ raw16357step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16357step1 raw16357step1Labels raw16357step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5016 node5016Labels := by rfl

def raw16358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw16358step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16358step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw16358step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16358 raw16358Labels = mixedMoment B node5006 node5006Labels := by
  calc
    mixedMoment B raw16358 raw16358Labels = mixedMoment B raw16358step0 raw16358step0Labels := by
      have hz : ∀ j, raw16358 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16358step0 = (fun i j => raw16358 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16358step0 raw16358; decide +kernel
      have hl : raw16358step0Labels = raw16358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16358 raw16358Labels permutation346 hz
    mixedMoment B raw16358step0 raw16358step0Labels = mixedMoment B raw16358step1 raw16358step1Labels := by
      have ha : raw16358step1 = (fun i j => raw16358step0 (permutation123 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16358step1 raw16358step0; decide +kernel
      have hl : raw16358step1Labels = raw16358step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16358step0 raw16358step0Labels permutation123 permutation5
    mixedMoment B raw16358step1 raw16358step1Labels = mixedMoment B raw16358step2 raw16358step2Labels := by
      have ha : raw16358step2 = raw16358step1 := by apply Matrix.ext; unfold raw16358step2 raw16358step1; decide +kernel
      have hl : raw16358step1Labels = labelEmbedding8 ∘ raw16358step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16358step1 raw16358step1Labels raw16358step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5006 node5006Labels := by rfl

def raw16359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16359step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16359step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw16359step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16359 raw16359Labels = mixedMoment B node5005 node5005Labels := by
  calc
    mixedMoment B raw16359 raw16359Labels = mixedMoment B raw16359step0 raw16359step0Labels := by
      have ha : raw16359step0 = (fun i j => raw16359 (permutation574 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16359step0 raw16359; decide +kernel
      have hl : raw16359step0Labels = raw16359Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16359 raw16359Labels permutation574 permutation5
    mixedMoment B raw16359step0 raw16359step0Labels = mixedMoment B raw16359step1 raw16359step1Labels := by
      have ha : raw16359step1 = raw16359step0 := by apply Matrix.ext; unfold raw16359step1 raw16359step0; decide +kernel
      have hl : raw16359step0Labels = labelEmbedding8 ∘ raw16359step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16359step0 raw16359step0Labels raw16359step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5005 node5005Labels := by rfl

def raw16360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![2, -3, 1], ![2, -1, -1]]
def raw16360step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16360step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16360step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw16360step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16360 raw16360Labels = mixedMoment B node5010 node5010Labels := by
  calc
    mixedMoment B raw16360 raw16360Labels = mixedMoment B raw16360step0 raw16360step0Labels := by
      have hz : ∀ j, raw16360 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16360step0 = (fun i j => raw16360 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16360step0 raw16360; decide +kernel
      have hl : raw16360step0Labels = raw16360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16360 raw16360Labels permutation346 hz
    mixedMoment B raw16360step0 raw16360step0Labels = mixedMoment B raw16360step1 raw16360step1Labels := by
      have ha : raw16360step1 = (fun i j => raw16360step0 (permutation122 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16360step1 raw16360step0; decide +kernel
      have hl : raw16360step1Labels = raw16360step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16360step0 raw16360step0Labels permutation122 permutation5
    mixedMoment B raw16360step1 raw16360step1Labels = mixedMoment B raw16360step2 raw16360step2Labels := by
      have ha : raw16360step2 = raw16360step1 := by apply Matrix.ext; unfold raw16360step2 raw16360step1; decide +kernel
      have hl : raw16360step1Labels = labelEmbedding8 ∘ raw16360step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16360step1 raw16360step1Labels raw16360step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5010 node5010Labels := by rfl

def raw16361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw16361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw16361step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16361step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw16361step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw16361step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16361 raw16361Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw16361 raw16361Labels = mixedMoment B raw16361step0 raw16361step0Labels := by
      have hz : ∀ j, raw16361 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16361step0 = (fun i j => raw16361 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16361step0 raw16361; decide +kernel
      have hl : raw16361step0Labels = raw16361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16361 raw16361Labels permutation346 hz
    mixedMoment B raw16361step0 raw16361step0Labels = mixedMoment B raw16361step1 raw16361step1Labels := by
      have ha : raw16361step1 = (fun i j => raw16361step0 (permutation123 i) (permutation5 j)) := by apply Matrix.ext; unfold raw16361step1 raw16361step0; decide +kernel
      have hl : raw16361step1Labels = raw16361step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16361step0 raw16361step0Labels permutation123 permutation5
    mixedMoment B raw16361step1 raw16361step1Labels = mixedMoment B raw16361step2 raw16361step2Labels := by
      have ha : raw16361step2 = raw16361step1 := by apply Matrix.ext; unfold raw16361step2 raw16361step1; decide +kernel
      have hl : raw16361step1Labels = labelEmbedding8 ∘ raw16361step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16361step1 raw16361step1Labels raw16361step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw16362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16362step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw16362step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw16362step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16362step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw16362step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16362 raw16362Labels = mixedMoment B node5001 node5001Labels := by
  calc
    mixedMoment B raw16362 raw16362Labels = mixedMoment B raw16362step0 raw16362step0Labels := by
      have hz : ∀ j, raw16362 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16362step0 = (fun i j => raw16362 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16362step0 raw16362; decide +kernel
      have hl : raw16362step0Labels = raw16362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16362 raw16362Labels permutation346 hz
    mixedMoment B raw16362step0 raw16362step0Labels = mixedMoment B raw16362step1 raw16362step1Labels := by
      have ha : raw16362step1 = (fun i j => raw16362step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16362step1 raw16362step0; decide +kernel
      have hl : raw16362step1Labels = raw16362step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16362step0 raw16362step0Labels permutation151 permutation3
    mixedMoment B raw16362step1 raw16362step1Labels = mixedMoment B raw16362step2 raw16362step2Labels := by
      have ha : raw16362step2 = -raw16362step1 := by apply Matrix.ext; change ∀ i j, raw16362step2 i j = -(raw16362step1 i j); unfold raw16362step2 raw16362step1; decide +kernel
      have hl : raw16362step2Labels = raw16362step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16362step2 raw16362step2Labels = mixedMoment B raw16362step3 raw16362step3Labels := by
      have ha : raw16362step3 = raw16362step2 := by apply Matrix.ext; unfold raw16362step3 raw16362step2; decide +kernel
      have hl : raw16362step2Labels = labelEmbedding6 ∘ raw16362step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16362step2 raw16362step2Labels raw16362step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5001 node5001Labels := by rfl

def raw16363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16363step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw16363step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw16363step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16363step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw16363step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16363 raw16363Labels = mixedMoment B node5002 node5002Labels := by
  calc
    mixedMoment B raw16363 raw16363Labels = mixedMoment B raw16363step0 raw16363step0Labels := by
      have hz : ∀ j, raw16363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16363step0 = (fun i j => raw16363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16363step0 raw16363; decide +kernel
      have hl : raw16363step0Labels = raw16363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16363 raw16363Labels permutation346 hz
    mixedMoment B raw16363step0 raw16363step0Labels = mixedMoment B raw16363step1 raw16363step1Labels := by
      have ha : raw16363step1 = (fun i j => raw16363step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16363step1 raw16363step0; decide +kernel
      have hl : raw16363step1Labels = raw16363step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16363step0 raw16363step0Labels permutation150 permutation3
    mixedMoment B raw16363step1 raw16363step1Labels = mixedMoment B raw16363step2 raw16363step2Labels := by
      have ha : raw16363step2 = -raw16363step1 := by apply Matrix.ext; change ∀ i j, raw16363step2 i j = -(raw16363step1 i j); unfold raw16363step2 raw16363step1; decide +kernel
      have hl : raw16363step2Labels = raw16363step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16363step2 raw16363step2Labels = mixedMoment B raw16363step3 raw16363step3Labels := by
      have ha : raw16363step3 = raw16363step2 := by apply Matrix.ext; unfold raw16363step3 raw16363step2; decide +kernel
      have hl : raw16363step2Labels = labelEmbedding6 ∘ raw16363step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16363step2 raw16363step2Labels raw16363step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5002 node5002Labels := by rfl

def raw16364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16364step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16364step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16364step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16364step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16364step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16364step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16364 raw16364Labels = mixedMoment B node4999 node4999Labels := by
  calc
    mixedMoment B raw16364 raw16364Labels = mixedMoment B raw16364step0 raw16364step0Labels := by
      have ha : raw16364step0 = (fun i j => raw16364 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16364step0 raw16364; decide +kernel
      have hl : raw16364step0Labels = raw16364Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16364 raw16364Labels permutation688 permutation3
    mixedMoment B raw16364step0 raw16364step0Labels = mixedMoment B raw16364step1 raw16364step1Labels := by
      have ha : raw16364step1 = -raw16364step0 := by apply Matrix.ext; change ∀ i j, raw16364step1 i j = -(raw16364step0 i j); unfold raw16364step1 raw16364step0; decide +kernel
      have hl : raw16364step1Labels = raw16364step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16364step1 raw16364step1Labels = mixedMoment B raw16364step2 raw16364step2Labels := by
      have ha : raw16364step2 = raw16364step1 := by apply Matrix.ext; unfold raw16364step2 raw16364step1; decide +kernel
      have hl : raw16364step1Labels = labelEmbedding6 ∘ raw16364step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16364step1 raw16364step1Labels raw16364step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4999 node4999Labels := by rfl

def raw16365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -2, 1], ![3, -2, -1]]
def raw16365step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw16365step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16365step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16365step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16365step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16365step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16365 raw16365Labels = mixedMoment B node5020 node5020Labels := by
  calc
    mixedMoment B raw16365 raw16365Labels = mixedMoment B raw16365step0 raw16365step0Labels := by
      have hz : ∀ j, raw16365 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16365step0 = (fun i j => raw16365 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16365step0 raw16365; decide +kernel
      have hl : raw16365step0Labels = raw16365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16365 raw16365Labels permutation346 hz
    mixedMoment B raw16365step0 raw16365step0Labels = mixedMoment B raw16365step1 raw16365step1Labels := by
      have ha : raw16365step1 = (fun i j => raw16365step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16365step1 raw16365step0; decide +kernel
      have hl : raw16365step1Labels = raw16365step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16365step0 raw16365step0Labels permutation149 permutation3
    mixedMoment B raw16365step1 raw16365step1Labels = mixedMoment B raw16365step2 raw16365step2Labels := by
      have ha : raw16365step2 = -raw16365step1 := by apply Matrix.ext; change ∀ i j, raw16365step2 i j = -(raw16365step1 i j); unfold raw16365step2 raw16365step1; decide +kernel
      have hl : raw16365step2Labels = raw16365step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16365step2 raw16365step2Labels = mixedMoment B raw16365step3 raw16365step3Labels := by
      have ha : raw16365step3 = raw16365step2 := by apply Matrix.ext; unfold raw16365step3 raw16365step2; decide +kernel
      have hl : raw16365step2Labels = labelEmbedding6 ∘ raw16365step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16365step2 raw16365step2Labels raw16365step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5020 node5020Labels := by rfl

def raw16366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw16366Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![3, -2, -1]]
def raw16366step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw16366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16366step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16366step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16366step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw16366step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16366step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical16366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16366 raw16366Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw16366 raw16366Labels = mixedMoment B raw16366step0 raw16366step0Labels := by
      have hz : ∀ j, raw16366 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16366step0 = (fun i j => raw16366 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16366step0 raw16366; decide +kernel
      have hl : raw16366step0Labels = raw16366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16366 raw16366Labels permutation346 hz
    mixedMoment B raw16366step0 raw16366step0Labels = mixedMoment B raw16366step1 raw16366step1Labels := by
      have ha : raw16366step1 = (fun i j => raw16366step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16366step1 raw16366step0; decide +kernel
      have hl : raw16366step1Labels = raw16366step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16366step0 raw16366step0Labels permutation151 permutation3
    mixedMoment B raw16366step1 raw16366step1Labels = mixedMoment B raw16366step2 raw16366step2Labels := by
      have ha : raw16366step2 = -raw16366step1 := by apply Matrix.ext; change ∀ i j, raw16366step2 i j = -(raw16366step1 i j); unfold raw16366step2 raw16366step1; decide +kernel
      have hl : raw16366step2Labels = raw16366step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw16366step2 raw16366step2Labels = mixedMoment B raw16366step3 raw16366step3Labels := by
      have ha : raw16366step3 = raw16366step2 := by apply Matrix.ext; unfold raw16366step3 raw16366step2; decide +kernel
      have hl : raw16366step2Labels = labelEmbedding6 ∘ raw16366step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw16366step2 raw16366step2Labels raw16366step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw16367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16367step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16367 raw16367Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw16367 raw16367Labels = mixedMoment B raw16367step0 raw16367step0Labels := by
      have hz : ∀ j, raw16367 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16367step0 = (fun i j => raw16367 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16367step0 raw16367; decide +kernel
      have hl : raw16367step0Labels = raw16367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16367 raw16367Labels permutation346 hz
    mixedMoment B raw16367step0 raw16367step0Labels = mixedMoment B raw16367step1 raw16367step1Labels := by
      have ha : raw16367step1 = (fun i j => raw16367step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16367step1 raw16367step0; decide +kernel
      have hl : raw16367step1Labels = raw16367step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16367step0 raw16367step0Labels permutation56 permutation3
    _ = mixedMoment B node3565 node3565Labels := by rfl

def raw16368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16368step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16368 raw16368Labels = mixedMoment B node3955 node3955Labels := by
  calc
    mixedMoment B raw16368 raw16368Labels = mixedMoment B raw16368step0 raw16368step0Labels := by
      have ha : raw16368step0 = (fun i j => raw16368 (permutation684 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16368step0 raw16368; decide +kernel
      have hl : raw16368step0Labels = raw16368Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16368 raw16368Labels permutation684 permutation3
    mixedMoment B raw16368step0 raw16368step0Labels = mixedMoment B raw16368step1 raw16368step1Labels := by
      have ha : raw16368step1 = -raw16368step0 := by apply Matrix.ext; change ∀ i j, raw16368step1 i j = -(raw16368step0 i j); unfold raw16368step1 raw16368step0; decide +kernel
      have hl : raw16368step1Labels = raw16368step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3955 node3955Labels := by rfl

def raw16369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw16369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16369step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw16369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16369 raw16369Labels = mixedMoment B node3960 node3960Labels := by
  calc
    mixedMoment B raw16369 raw16369Labels = mixedMoment B raw16369step0 raw16369step0Labels := by
      have hz : ∀ j, raw16369 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16369step0 = (fun i j => raw16369 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16369step0 raw16369; decide +kernel
      have hl : raw16369step0Labels = raw16369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16369 raw16369Labels permutation346 hz
    mixedMoment B raw16369step0 raw16369step0Labels = mixedMoment B raw16369step1 raw16369step1Labels := by
      have ha : raw16369step1 = (fun i j => raw16369step0 (permutation146 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16369step1 raw16369step0; decide +kernel
      have hl : raw16369step1Labels = raw16369step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16369step0 raw16369step0Labels permutation146 permutation3
    mixedMoment B raw16369step1 raw16369step1Labels = mixedMoment B raw16369step2 raw16369step2Labels := by
      have ha : raw16369step2 = -raw16369step1 := by apply Matrix.ext; change ∀ i j, raw16369step2 i j = -(raw16369step1 i j); unfold raw16369step2 raw16369step1; decide +kernel
      have hl : raw16369step2Labels = raw16369step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3960 node3960Labels := by rfl

def raw16370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw16370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16370step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw16370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16370 raw16370Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw16370 raw16370Labels = mixedMoment B raw16370step0 raw16370step0Labels := by
      have hz : ∀ j, raw16370 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16370step0 = (fun i j => raw16370 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16370step0 raw16370; decide +kernel
      have hl : raw16370step0Labels = raw16370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16370 raw16370Labels permutation346 hz
    mixedMoment B raw16370step0 raw16370step0Labels = mixedMoment B raw16370step1 raw16370step1Labels := by
      have ha : raw16370step1 = (fun i j => raw16370step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16370step1 raw16370step0; decide +kernel
      have hl : raw16370step1Labels = raw16370step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16370step0 raw16370step0Labels permutation49 permutation6
    mixedMoment B raw16370step1 raw16370step1Labels = mixedMoment B raw16370step2 raw16370step2Labels := by
      have ha : raw16370step2 = -raw16370step1 := by apply Matrix.ext; change ∀ i j, raw16370step2 i j = -(raw16370step1 i j); unfold raw16370step2 raw16370step1; decide +kernel
      have hl : raw16370step2Labels = raw16370step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw16371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw16371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16371step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16371 raw16371Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw16371 raw16371Labels = mixedMoment B raw16371step0 raw16371step0Labels := by
      have hz : ∀ j, raw16371 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16371step0 = (fun i j => raw16371 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16371step0 raw16371; decide +kernel
      have hl : raw16371step0Labels = raw16371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16371 raw16371Labels permutation346 hz
    mixedMoment B raw16371step0 raw16371step0Labels = mixedMoment B raw16371step1 raw16371step1Labels := by
      have ha : raw16371step1 = (fun i j => raw16371step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16371step1 raw16371step0; decide +kernel
      have hl : raw16371step1Labels = raw16371step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16371step0 raw16371step0Labels permutation49 permutation6
    mixedMoment B raw16371step1 raw16371step1Labels = mixedMoment B raw16371step2 raw16371step2Labels := by
      have ha : raw16371step2 = -raw16371step1 := by apply Matrix.ext; change ∀ i j, raw16371step2 i j = -(raw16371step1 i j); unfold raw16371step2 raw16371step1; decide +kernel
      have hl : raw16371step2Labels = raw16371step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw16372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw16372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16372 raw16372Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw16372 raw16372Labels = mixedMoment B raw16372step0 raw16372step0Labels := by
      have hz : ∀ j, raw16372 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16372step0 = (fun i j => raw16372 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16372step0 raw16372; decide +kernel
      have hl : raw16372step0Labels = raw16372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16372 raw16372Labels permutation346 hz
    mixedMoment B raw16372step0 raw16372step0Labels = mixedMoment B raw16372step1 raw16372step1Labels := by
      have ha : raw16372step1 = (fun i j => raw16372step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16372step1 raw16372step0; decide +kernel
      have hl : raw16372step1Labels = raw16372step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16372step0 raw16372step0Labels permutation32 permutation3
    _ = mixedMoment B node3078 node3078Labels := by rfl

def raw16373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw16373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw16373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16373 raw16373Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw16373 raw16373Labels = mixedMoment B raw16373step0 raw16373step0Labels := by
      have ha : raw16373step0 = (fun i j => raw16373 (permutation676 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16373step0 raw16373; decide +kernel
      have hl : raw16373step0Labels = raw16373Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16373 raw16373Labels permutation676 permutation3
    mixedMoment B raw16373step0 raw16373step0Labels = mixedMoment B raw16373step1 raw16373step1Labels := by
      have ha : raw16373step1 = -raw16373step0 := by apply Matrix.ext; change ∀ i j, raw16373step1 i j = -(raw16373step0 i j); unfold raw16373step1 raw16373step0; decide +kernel
      have hl : raw16373step1Labels = raw16373step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3954 node3954Labels := by rfl

def raw16374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16374step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16374step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16374step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16374 raw16374Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw16374 raw16374Labels = mixedMoment B raw16374step0 raw16374step0Labels := by
      have hz : ∀ j, raw16374 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16374step0 = (fun i j => raw16374 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16374step0 raw16374; decide +kernel
      have hl : raw16374step0Labels = raw16374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16374 raw16374Labels permutation346 hz
    mixedMoment B raw16374step0 raw16374step0Labels = mixedMoment B raw16374step1 raw16374step1Labels := by
      have ha : raw16374step1 = (fun i j => raw16374step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16374step1 raw16374step0; decide +kernel
      have hl : raw16374step1Labels = raw16374step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16374step0 raw16374step0Labels permutation149 permutation3
    mixedMoment B raw16374step1 raw16374step1Labels = mixedMoment B raw16374step2 raw16374step2Labels := by
      have ha : raw16374step2 = -raw16374step1 := by apply Matrix.ext; change ∀ i j, raw16374step2 i j = -(raw16374step1 i j); unfold raw16374step2 raw16374step1; decide +kernel
      have hl : raw16374step2Labels = raw16374step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw16375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16375step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16375step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw16375step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16375step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw16375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16375 raw16375Labels = mixedMoment B node4012 node4012Labels := by
  calc
    mixedMoment B raw16375 raw16375Labels = mixedMoment B raw16375step0 raw16375step0Labels := by
      have hz : ∀ j, raw16375 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16375step0 = (fun i j => raw16375 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16375step0 raw16375; decide +kernel
      have hl : raw16375step0Labels = raw16375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16375 raw16375Labels permutation346 hz
    mixedMoment B raw16375step0 raw16375step0Labels = mixedMoment B raw16375step1 raw16375step1Labels := by
      have ha : raw16375step1 = (fun i j => raw16375step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16375step1 raw16375step0; decide +kernel
      have hl : raw16375step1Labels = raw16375step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16375step0 raw16375step0Labels permutation149 permutation3
    mixedMoment B raw16375step1 raw16375step1Labels = mixedMoment B raw16375step2 raw16375step2Labels := by
      have ha : raw16375step2 = -raw16375step1 := by apply Matrix.ext; change ∀ i j, raw16375step2 i j = -(raw16375step1 i j); unfold raw16375step2 raw16375step1; decide +kernel
      have hl : raw16375step2Labels = raw16375step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4012 node4012Labels := by rfl

def raw16376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw16376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16376step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw16376step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16376 raw16376Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw16376 raw16376Labels = mixedMoment B raw16376step0 raw16376step0Labels := by
      have hz : ∀ j, raw16376 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16376step0 = (fun i j => raw16376 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16376step0 raw16376; decide +kernel
      have hl : raw16376step0Labels = raw16376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16376 raw16376Labels permutation346 hz
    mixedMoment B raw16376step0 raw16376step0Labels = mixedMoment B raw16376step1 raw16376step1Labels := by
      have ha : raw16376step1 = (fun i j => raw16376step0 (permutation48 i) (permutation6 j)) := by apply Matrix.ext; unfold raw16376step1 raw16376step0; decide +kernel
      have hl : raw16376step1Labels = raw16376step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16376step0 raw16376step0Labels permutation48 permutation6
    mixedMoment B raw16376step1 raw16376step1Labels = mixedMoment B raw16376step2 raw16376step2Labels := by
      have ha : raw16376step2 = -raw16376step1 := by apply Matrix.ext; change ∀ i j, raw16376step2 i j = -(raw16376step1 i j); unfold raw16376step2 raw16376step1; decide +kernel
      have hl : raw16376step2Labels = raw16376step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw16377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16377 raw16377Labels = mixedMoment B node2854 node2854Labels := by
  calc
    mixedMoment B raw16377 raw16377Labels = mixedMoment B raw16377step0 raw16377step0Labels := by
      have ha : raw16377step0 = (fun i j => raw16377 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16377step0 raw16377; decide +kernel
      have hl : raw16377step0Labels = raw16377Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16377 raw16377Labels permutation158 permutation3
    _ = mixedMoment B node2854 node2854Labels := by rfl

def raw16378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw16378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16378 raw16378Labels = mixedMoment B node3371 node3371Labels := by
  calc
    mixedMoment B raw16378 raw16378Labels = mixedMoment B raw16378step0 raw16378step0Labels := by
      have ha : raw16378step0 = (fun i j => raw16378 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16378step0 raw16378; decide +kernel
      have hl : raw16378step0Labels = raw16378Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16378 raw16378Labels permutation271 permutation3
    _ = mixedMoment B node3371 node3371Labels := by rfl

def raw16379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, 0, -1], ![-1, -1, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw16379step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw16379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16379 raw16379Labels = mixedMoment B node3943 node3943Labels := by
  calc
    mixedMoment B raw16379 raw16379Labels = mixedMoment B raw16379step0 raw16379step0Labels := by
      have ha : raw16379step0 = (fun i j => raw16379 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16379step0 raw16379; decide +kernel
      have hl : raw16379step0Labels = raw16379Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16379 raw16379Labels permutation680 permutation3
    mixedMoment B raw16379step0 raw16379step0Labels = mixedMoment B raw16379step1 raw16379step1Labels := by
      have ha : raw16379step1 = -raw16379step0 := by apply Matrix.ext; change ∀ i j, raw16379step1 i j = -(raw16379step0 i j); unfold raw16379step1 raw16379step0; decide +kernel
      have hl : raw16379step1Labels = raw16379step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3943 node3943Labels := by rfl

def raw16380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -1, -1]]
def raw16380Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw16380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw16380step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw16380step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16380 raw16380Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw16380 raw16380Labels = mixedMoment B raw16380step0 raw16380step0Labels := by
      have ha : raw16380step0 = (fun i j => raw16380 (permutation646 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16380step0 raw16380; decide +kernel
      have hl : raw16380step0Labels = raw16380Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16380 raw16380Labels permutation646 permutation3
    mixedMoment B raw16380step0 raw16380step0Labels = mixedMoment B raw16380step1 raw16380step1Labels := by
      have ha : raw16380step1 = -raw16380step0 := by apply Matrix.ext; change ∀ i j, raw16380step1 i j = -(raw16380step0 i j); unfold raw16380step1 raw16380step0; decide +kernel
      have hl : raw16380step1Labels = raw16380step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw16381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw16381Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw16381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16381 raw16381Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw16381 raw16381Labels = mixedMoment B raw16381step0 raw16381step0Labels := by
      have ha : raw16381step0 = (fun i j => raw16381 (permutation162 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16381step0 raw16381; decide +kernel
      have hl : raw16381step0Labels = raw16381Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16381 raw16381Labels permutation162 permutation3
    _ = mixedMoment B node4024 node4024Labels := by rfl

def raw16382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16382step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16382 raw16382Labels = mixedMoment B node2882 node2882Labels := by
  calc
    mixedMoment B raw16382 raw16382Labels = mixedMoment B raw16382step0 raw16382step0Labels := by
      have hz : ∀ j, raw16382 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16382step0 = (fun i j => raw16382 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16382step0 raw16382; decide +kernel
      have hl : raw16382step0Labels = raw16382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16382 raw16382Labels permutation346 hz
    mixedMoment B raw16382step0 raw16382step0Labels = mixedMoment B raw16382step1 raw16382step1Labels := by
      have ha : raw16382step1 = (fun i j => raw16382step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16382step1 raw16382step0; decide +kernel
      have hl : raw16382step1Labels = raw16382step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16382step0 raw16382step0Labels permutation32 permutation3
    _ = mixedMoment B node2882 node2882Labels := by rfl

def raw16383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw16383step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw16383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw16383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical16383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw16383 raw16383Labels = mixedMoment B node3392 node3392Labels := by
  calc
    mixedMoment B raw16383 raw16383Labels = mixedMoment B raw16383step0 raw16383step0Labels := by
      have hz : ∀ j, raw16383 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw16383step0 = (fun i j => raw16383 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw16383step0 raw16383; decide +kernel
      have hl : raw16383step0Labels = raw16383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw16383 raw16383Labels permutation346 hz
    mixedMoment B raw16383step0 raw16383step0Labels = mixedMoment B raw16383step1 raw16383step1Labels := by
      have ha : raw16383step1 = (fun i j => raw16383step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw16383step1 raw16383step0; decide +kernel
      have hl : raw16383step1Labels = raw16383step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw16383step0 raw16383step0Labels permutation56 permutation3
    _ = mixedMoment B node3392 node3392Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
